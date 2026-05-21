/-
# Counterfactuals.lean — Formalization of UNSAT-Diagram Semantics

This file mechanizes the counterfactual layout semantics described in
**§5 (Constraint (Dis)Satisfaction)** of the PLDI 2026 paper, together
with the corresponding runtime in `spytial-core`. It extends `Main.lean`
(which mechanizes §4 (Formalizing Spytial)).

## Why this file exists

`Main.lean` proves `unsat_iff_empty` (§4.4, paper line 1164):
  `⟦P⟧ = ∅ ↔ ∀ R ∈ WF, ¬ modelsP R P`

When `⟦P⟧ = ∅`, the user has given an over-constrained spec and there is
*no* realization to draw. Yet **spytial-core still renders a diagram** —
the counterfactual diagram (paper §5.2, line 1353; intro contribution
line 450-452; abstract line 297). This file formalizes:

  (1) what such a diagram is, semantically;
  (2) which constraints it satisfies (the **MFS** — kept) and which it
      drops (the **IIS** — dual hitting set);
  (3) under what conditions a diagram exists, and what guarantees it
      provides.

## Paper ↔ Lean ↔ spytial-core correspondence

| Concept                       | Paper                              | Lean (this file)                       | spytial-core (TypeScript)                                            |
|-------------------------------|------------------------------------|----------------------------------------|----------------------------------------------------------------------|
| Feasibility                   | §4.4 "denotation nonempty"         | `Feasible P`                           | `(denotes M).Nonempty` check in validators                           |
| Irreducible Infeasible Subsys | §5.1 (line 1199)                   | `IsIIS P I`                            | `minimalConflictingSet` in `constraint-validator.ts`                 |
| quasi-IIS (subset-minimal)    | §5.1 (line 1250)                   | `IsIIS` (same — minimality is the same definition) | `getMinimalDisjunctiveConflict` in `constraint-validator.ts:1143` |
| Maximal Feasible Subset       | §5.2 (dual, implicit)              | `IsMFS P M`                            | `computeMaximalFeasibleSubset` in `qualitative-constraint-validator.ts` |
| Counterfactual diagram        | §5.2 "Layout level" (line 1353)    | `counterfactual P`  (notation `⟦P⟧₊`)  | `CounterfactualLayoutResult` in `layoutinstance.ts`                  |
| Cut-out constraints           | §5.2 "relaxing inequalities"       | `droppedConstraints P M`               | `layout.constraints.filter(...)` in `layoutinstance.ts:1424`         |
| Conflict overlay              | §5.2 "Diagram Element / Constraint levels" | (annotation; not modeled here) | `CounterfactualLayoutResult.conflictingConstraints`                  |

## A subtle point: IIS-relaxation (paper) vs MFS-keeping (spytial-core)

The paper (§5.2, line 1353) describes the counterfactual diagram as
"relaxing all solver-level inequalities in the IIS". That removes one
quasi-IIS from the program and re-solves.

spytial-core's **qualitative validator** (the default since the
re-architecture) instead computes a global **MFS** and removes its
complement. These two strategies are **not equivalent**:

* **MFS-keeping** is feasible *by construction* (`mfs_kept_is_feasible`).
* **IIS-removal** is *not* guaranteed feasible: removing a single IIS
  `I` leaves `P \ I`, which can still contain another IIS (theorem
  `iis_removal_can_remain_infeasible` — when two IISes are disjoint,
  removing one preserves the other's infeasibility).

A single MFS pass breaks **every** IIS simultaneously (via the
hitting-set property `mfs_hits_every_iis`); a single IIS pass breaks
only the chosen one. The paper's strategy is therefore an *iterative*
relaxation (one IIS at a time, until feasible), while spytial-core's
qualitative validator computes the feasible target in one pass.

## File outline

1.  **Feasibility** (`Feasible`)                       — basic predicate.
2.  **IIS** (`IsIIS`)                                  — paper §5.1.
3.  **MFS** (`IsMFS`)                                  — dual of IIS.
4.  **Duality** (`mfs_hits_every_iis`)                 — the bridge theorem.
5.  **Counterfactual denotation** (`⟦P⟧₊`)             — paper §5.2 "Layout level".
6.  **Cut-out set** (`droppedConstraints`)             — paper "relaxing".

Extends `Main.lean`.
-/

import Main
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Spytial
namespace Counterfactual

--------------------------------------------------------------------------------
-- 1. Feasibility                                                  (paper §4.4)
--------------------------------------------------------------------------------

/-- A program is **feasible** iff its denotation is inhabited — i.e., there
    is at least one well-formed realization satisfying every qualified
    constraint.

    This is the positive dual of "unsatisfiable" as formalized in
    `Main.lean` via `unsat_iff_empty` (paper line 1164):
      `⟦P⟧ = ∅ ↔ ∀ R ∈ WF, ¬ modelsP R P`
    (Lean's `modelsP` is the program-level lift of constraint satisfaction;
    the paper writes this with `\modelsC` — same notion, different name.)
    Hence `Feasible P ↔ ¬ (⟦P⟧ = ∅) ↔ ∃ R ∈ WF, modelsP R P`. -/
def Feasible (P : Program) : Prop := (denotes P).Nonempty

/-- **Antimonotonicity of feasibility.** Removing constraints preserves
    feasibility. Direct corollary of `antimonotonicity` in `Main.lean`
    (paper §4.4, equation on line 1157). -/
lemma feasible_of_subset {P Q : Program} (hPQ : P ⊆ Q) (hQ : Feasible Q) :
    Feasible P :=
  hQ.mono (antimonotonicity hPQ)

/-- The empty program is feasible iff `WF` is inhabited.
    Combines `denotes_empty : ⟦∅⟧ = WF` (Main.lean) with the definition. -/
lemma empty_feasible_iff : Feasible (∅ : Program) ↔ WF.Nonempty := by
  unfold Feasible
  rw [denotes_empty]

--------------------------------------------------------------------------------
-- 2. Irreducible Infeasible Subsystem (IIS)                       (paper §5.1)
--------------------------------------------------------------------------------

/-- `I` is an **Irreducible Infeasible Subsystem** of `P` iff:
    (1) `I ⊆ P`,
    (2) `I` is infeasible (jointly contradictory), and
    (3) removing any single constraint of `I` makes it feasible.

    This is the paper's definition verbatim (§5.1, lines 1207-1208):
    *"An IIS is a minimal subset of constraints that cannot be satisfied
    together, even though every proper subset is feasible."*

    The paper's runtime computes a **quasi-IIS** by iterative deletion
    (§5.1, line 1250). The quasi-IIS is subset-minimal — i.e., it
    satisfies (3) — but smaller IISes may exist elsewhere in `P`
    (line 1256). Our `IsIIS` predicate captures exactly subset-minimality,
    matching the quasi-IIS notion used by `spytial-core`. -/
def IsIIS (P I : Program) : Prop :=
  I ⊆ P ∧ ¬ Feasible I ∧ ∀ c ∈ I, Feasible (I.erase c)

namespace IsIIS
lemma subset {P I : Program} (h : IsIIS P I) : I ⊆ P := h.1
lemma infeasible {P I : Program} (h : IsIIS P I) : ¬ Feasible I := h.2.1
lemma erase_feasible {P I : Program} (h : IsIIS P I) :
    ∀ c ∈ I, Feasible (I.erase c) := h.2.2
end IsIIS

/-- **No IIS in a feasible program.** A trivial sanity check: if `P` itself
    has a satisfying realization, then no infeasible-minimal subsystem can
    exist within it. -/
lemma no_iis_of_feasible {P : Program} (hSat : Feasible P) :
    ¬ ∃ I, IsIIS P I := by
  rintro ⟨I, hIP, hInfeas, _⟩
  exact hInfeas (feasible_of_subset hIP hSat)

/-- **Existence of an IIS.** When `P` is infeasible, `P` admits at least
    one IIS.

    *Proof technique.* We construct an IIS as a **minimum-cardinality**
    infeasible subset of `P` (which exists because `P` itself is in that
    family). Such a set is automatically subset-minimal: any strict subset
    has smaller cardinality, so it cannot be in the family — i.e., it is
    feasible.

    This existence proof is **non-constructive**: it does not match the
    paper's iterative-deletion algorithm (§5.1, line 1250-1256), but
    certifies that the algorithm's target is well-defined. The paper's
    procedure produces *some* subset-minimal infeasible subset, not
    necessarily one of minimum cardinality — both are IISes by our
    definition. -/
theorem iis_exists_of_infeasible (P : Program) (hUnsat : ¬ Feasible P) :
    ∃ I, IsIIS P I := by
  classical
  -- The family of infeasible subsets of P. P itself is in this family.
  have hP_in_F :
      P ∈ P.powerset.filter (fun I => ¬ (denotes I).Nonempty) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_refl P, hUnsat⟩
  -- Take a minimum-cardinality member of the family.
  obtain ⟨I, hI_mem, hI_min⟩ :=
    Finset.exists_min_image
      (P.powerset.filter (fun I => ¬ (denotes I).Nonempty))
      Finset.card ⟨P, hP_in_F⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hI_mem
  obtain ⟨hIP, hIInfeas⟩ := hI_mem
  refine ⟨I, hIP, hIInfeas, ?_⟩
  -- Show every single-element erasure of I is feasible.
  -- If I.erase c were infeasible, it would be a smaller member of the
  -- family — contradicting I's minimum cardinality.
  intros c hcI
  by_contra hErase_infeas
  have hErase_in :
      I.erase c ∈ P.powerset.filter (fun I => ¬ (denotes I).Nonempty) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.erase_subset c I).trans hIP, hErase_infeas⟩
  have hErase_card : (I.erase c).card < I.card :=
    Finset.card_erase_lt_of_mem hcI
  have h_le := hI_min (I.erase c) hErase_in
  omega

/-- **Characterization.** A program is infeasible iff it admits an IIS.
    This is the IIS-side analogue of `unsat_iff_empty` from `Main.lean`
    (paper §4.4, line 1164). -/
theorem unsat_iff_exists_iis (P : Program) :
    ¬ Feasible P ↔ ∃ I, IsIIS P I := by
  refine ⟨iis_exists_of_infeasible P, ?_⟩
  rintro ⟨I, hIP, hInfeas, _⟩ hFeas
  exact hInfeas (feasible_of_subset hIP hFeas)

/-- **Strong existence.** Every infeasible subset of `P` contains an IIS.
    Useful for reasoning about the search procedure in §5.1: whatever
    infeasible subsystem the solver isolates first, an IIS lurks inside. -/
theorem iis_subset_of_infeasible (P Q : Program) (hQP : Q ⊆ P)
    (hQUnsat : ¬ Feasible Q) : ∃ I, IsIIS P I ∧ I ⊆ Q := by
  classical
  obtain ⟨I, hIQ, hInfeas, hErase⟩ := iis_exists_of_infeasible Q hQUnsat
  exact ⟨I, ⟨hIQ.trans hQP, hInfeas, hErase⟩, hIQ⟩

--------------------------------------------------------------------------------
-- 3. Maximal Feasible Subset (MFS)                       (dual of §5.1's IIS)
--------------------------------------------------------------------------------

/-- `M` is a **Maximal Feasible Subset** of `P` iff:
    (1) `M ⊆ P`,
    (2) `M` is feasible, and
    (3) adjoining any further constraint of `P` to `M` makes it infeasible.

    The MFS is the **set of constraints kept** when rendering a
    counterfactual diagram; constraints in `P \ M` are *cut out*.

    *The paper vs. the runtime.* The PLDI paper (§5.2, line 1353) phrases
    counterfactual rendering as "relaxing all solver-level inequalities
    in the IIS" — i.e., remove the IIS, keep the rest. spytial-core's
    current default (the **qualitative validator**) instead computes a
    global MFS directly. By the duality theorem `mfs_hits_every_iis`
    (below), the MFS-complement is a hitting set for the entire IIS
    family — so MFS-keeping breaks *every* IIS in one shot, while
    IIS-removal breaks only the chosen IIS.

    *Single-step maximality.* Condition (3) checks only single-element
    extensions. This is equivalent to "no feasible strict superset
    exists" because `antimonotonicity` lifts feasibility down through
    arbitrary subsets — so the existence of *any* feasible superset
    implies the existence of a feasible *one-element* extension. -/
def IsMFS (P M : Program) : Prop :=
  M ⊆ P ∧ Feasible M ∧ ∀ c ∈ P, c ∉ M → ¬ Feasible (insert c M)

namespace IsMFS
lemma subset {P M : Program} (h : IsMFS P M) : M ⊆ P := h.1
lemma feasible {P M : Program} (h : IsMFS P M) : Feasible M := h.2.1
lemma maximal {P M : Program} (h : IsMFS P M) :
    ∀ c ∈ P, c ∉ M → ¬ Feasible (insert c M) := h.2.2
end IsMFS

/-- When `P` is feasible, `P` is itself an MFS (the only one). -/
lemma mfs_self_of_feasible {P : Program} (hSat : Feasible P) : IsMFS P P :=
  ⟨subset_refl P, hSat, fun _ hcP hcM => absurd hcP hcM⟩

/-- **Uniqueness under feasibility.** When `P` is feasible, *the only* MFS
    is `P` itself. Any strict subset would be non-maximal because the
    full program is a feasible extension (antimonotonicity). -/
lemma mfs_unique_of_feasible {P : Program} (hSat : Feasible P)
    {M : Program} (hMFS : IsMFS P M) : M = P := by
  by_contra hNe
  have hSS : M ⊂ P := Finset.ssubset_iff_subset_ne.mpr ⟨hMFS.subset, hNe⟩
  obtain ⟨c, hcP, hcM⟩ := Finset.exists_of_ssubset hSS
  -- If insert c M were feasible, it would contradict maximality.
  -- And it is feasible: insert c M ⊆ P, and P is feasible, so by
  -- antimonotonicity its denotation is nonempty.
  exact hMFS.maximal c hcP hcM
    (feasible_of_subset (Finset.insert_subset_iff.mpr ⟨hcP, hMFS.subset⟩) hSat)

/-- **Existence of MFS.** Every program admits at least one MFS, provided
    `WF.Nonempty` (so the empty subset is feasible and the family is
    nonempty).

    *Proof technique.* Take a feasible subset of **maximum cardinality**.
    Such a set is automatically maximal: any strict superset has greater
    cardinality, so cannot be in the family — i.e., is infeasible.

    Like `iis_exists_of_infeasible`, this is non-constructive and does
    not match the runtime's greedy algorithm (`computeMaximalFeasibleSubset`
    in `qualitative-constraint-validator.ts`). It proves the runtime's
    target is well-defined. -/
theorem mfs_exists (P : Program) (hWF : WF.Nonempty) : ∃ M, IsMFS P M := by
  classical
  -- The family of feasible subsets of P. ∅ is in this family (since WF ≠ ∅).
  have h_empty_feasible :
      (∅ : Program) ∈ P.powerset.filter (fun M => (denotes M).Nonempty) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset P, ?_⟩
    rw [denotes_empty]; exact hWF
  -- Take a maximum-cardinality member of the family.
  obtain ⟨M, hM_mem, hM_max⟩ :=
    Finset.exists_max_image (P.powerset.filter (fun M => (denotes M).Nonempty))
      Finset.card ⟨∅, h_empty_feasible⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hM_mem
  obtain ⟨hMP, hMFeas⟩ := hM_mem
  refine ⟨M, hMP, hMFeas, ?_⟩
  -- Maximality: if `insert c M` were feasible, it would be a larger member
  -- of the family — contradicting M's maximum cardinality.
  intros c hcP hcM hFeasIns
  have hIns_in_S :
      insert c M ∈ P.powerset.filter (fun M => (denotes M).Nonempty) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset_iff.mpr ⟨hcP, hMP⟩, hFeasIns⟩
  have hCard : M.card < (insert c M).card := by
    rw [Finset.card_insert_of_notMem hcM]; omega
  have h_le := hM_max (insert c M) hIns_in_S
  omega

--------------------------------------------------------------------------------
-- 4. MFS ↔ IIS Duality                                            (key result)
--------------------------------------------------------------------------------

/-- **Hitting-set duality.** Every MFS misses at least one constraint from
    every IIS. Equivalently: the *complement* of an MFS is a **hitting
    set** for the family of IISes — that is, every IIS contains at least
    one constraint that the MFS does not.

    *Why this is the central theorem of this file.* The paper (§5.2,
    line 1353) defines the counterfactual diagram by **removing the
    IIS**. spytial-core's current implementation instead **keeps the MFS**
    (drops the complement). These two strategies coexist in practice
    (cf. `layoutinstance.ts:1419-1421`), and this theorem proves they are
    compatible:

      *Cutting out the MFS-complement simultaneously breaks every IIS.*

    So the diagram produced by MFS-removal is "globally consistent" — it
    breaks every minimal conflict, not just the one the solver happened
    to find first. -/
theorem mfs_hits_every_iis {P M I : Program}
    (hMFS : IsMFS P M) (hIIS : IsIIS P I) :
    ∃ c ∈ I, c ∉ M := by
  by_contra hNo
  push_neg at hNo
  -- ¬ ∃ c ∈ I, c ∉ M   ⇒   I ⊆ M   ⇒   I is feasible (since M is).
  -- But I is an IIS, hence infeasible. Contradiction.
  exact hIIS.infeasible (feasible_of_subset hNo hMFS.feasible)

/-- **Hitting-set corollary, restated.** The constraints *dropped* from
    the diagram (`P \ M` for an MFS `M`) intersect every IIS — i.e., the
    drop set is a hitting set for the IIS family. Direct restatement of
    `mfs_hits_every_iis` in `droppedConstraints` form, useful when
    reasoning about the rendering pipeline. -/
theorem iis_complement_is_hitting_set {P M I : Program}
    (hMFS : IsMFS P M) (hIIS : IsIIS P I) :
    (I ∩ (P \ M)).Nonempty := by
  obtain ⟨c, hcI, hcM⟩ := mfs_hits_every_iis hMFS hIIS
  exact ⟨c, Finset.mem_inter.mpr ⟨hcI, Finset.mem_sdiff.mpr ⟨hIIS.subset hcI, hcM⟩⟩⟩

/-- **MFS-keeping yields feasibility by definition** — trivial restatement,
    but stated explicitly to make the contrast with IIS-removal sharp.
    The MFS `M` *is* the rendered program; it is feasible by `IsMFS.feasible`. -/
theorem mfs_kept_is_feasible {P M : Program} (hMFS : IsMFS P M) :
    Feasible M := hMFS.feasible

/-- **IIS-removal does NOT generally yield feasibility.** This formalizes
    the asymmetry between MFS-keeping and IIS-removal:

    * `mfs_kept_is_feasible` — removing the MFS-complement always leaves
      a feasible program.
    * This theorem — removing a single IIS need not, because *other*
      IISes can persist.

    *Witness condition.* If `P` contains two **disjoint** IISes `I₁` and
    `I₂`, then `P \ I₁` is still infeasible: `I₂ ⊆ P \ I₁` (since `I₂` is
    in `P` but disjoint from `I₁`), and `I₂` is infeasible by assumption,
    so by `feasible_of_subset` any superset of `I₂` is infeasible too.

    This is why spytial-core's qualitative validator uses MFS-keeping
    rather than iterative IIS-removal: a single MFS pass breaks every
    IIS simultaneously (`mfs_hits_every_iis`), whereas a single IIS pass
    only breaks the chosen one. -/
theorem iis_removal_can_remain_infeasible {P I₁ I₂ : Program}
    (_hI₁ : IsIIS P I₁) (hI₂ : IsIIS P I₂) (hDisj : Disjoint I₁ I₂) :
    ¬ Feasible (P \ I₁) := by
  -- (`_hI₁` unused in the proof — kept for semantic framing: the user's
  --  concern is specifically about removing an IIS. The proof itself
  --  only needs that I₂ is an IIS and I₁ is disjoint from I₂.)
  -- I₂ ⊆ P \ I₁ : I₂ ⊆ P (IIS) and I₂ ∩ I₁ = ∅ (disjoint).
  have hI₂_sub : I₂ ⊆ P \ I₁ := by
    intro c hc
    refine Finset.mem_sdiff.mpr ⟨hI₂.subset hc, ?_⟩
    intro hcI₁
    exact (Finset.disjoint_left.mp hDisj) hcI₁ hc
  -- If P \ I₁ were feasible, I₂ would inherit feasibility — contradicting
  -- the fact that I₂ is an IIS (hence infeasible).
  intro hFeas
  exact hI₂.infeasible (feasible_of_subset hI₂_sub hFeas)

--------------------------------------------------------------------------------
-- 5. Counterfactual Denotation                                    (paper §5.2)
--------------------------------------------------------------------------------

/-- The **counterfactual denotation** of `P` is the union of denotations
    of all its MFSes.

    Paper §5.2 (line 1353) calls this the *layout-level* counterfactual:
    > "Produce a counterfactual diagram by relaxing all solver-level
    >  inequalities in the IIS, and highlighting the boxes corresponding
    >  to variables involved."

    Two behaviours follow:
    * **SAT case** — `P` feasible: `⟦P⟧₊ = ⟦P⟧` (Theorem
      `counterfactual_eq_denotes_of_feasible`). Nothing is dropped; the
      user's spec is rendered verbatim.
    * **UNSAT case** — `P` infeasible: `⟦P⟧₊` collects realizations of
      every maximally-satisfiable fragment. The diagram realizes *some*
      MFS, with the complement annotated as "cut out".

    The set is *always inhabited* when `WF.Nonempty` (Theorem
    `counterfactual_nonempty`). This formalizes the design goal articulated
    in paper §5.2 line 1286-1287:
    > "Users need to know *when* and *why* a conflict occurs, but a
    >  partial visualization is often more informative than just a
    >  textual report of conflicting constraints." -/
def counterfactual (P : Program) : Set Realization :=
  { R | ∃ M, IsMFS P M ∧ R ∈ denotes M }

@[inherit_doc] notation "⟦" P "⟧₊" => counterfactual P

@[simp] lemma mem_counterfactual {P : Program} {R : Realization} :
    R ∈ ⟦P⟧₊ ↔ ∃ M, IsMFS P M ∧ R ∈ denotes M := Iff.rfl

/-- Equivalent presentation as a set-theoretic union over the family of
    MFSes. Useful for relating to spytial-core's pipeline, which
    materializes a *specific* MFS rather than the union — but the union
    is the right *semantic* object. -/
lemma counterfactual_eq_iUnion (P : Program) :
    ⟦P⟧₊ = ⋃ M ∈ {M : Program | IsMFS P M}, denotes M := by
  ext R
  constructor
  · rintro ⟨M, hMFS, hRM⟩
    refine Set.mem_iUnion.mpr ⟨M, ?_⟩
    exact Set.mem_iUnion.mpr ⟨hMFS, hRM⟩
  · intro hR
    obtain ⟨M, hR'⟩ := Set.mem_iUnion.mp hR
    obtain ⟨hMFS, hRM⟩ := Set.mem_iUnion.mp hR'
    exact ⟨M, hMFS, hRM⟩

/-- **Well-formedness.** Every counterfactual realization is well-formed
    in the sense of `Main.lean`'s `WF` (paper §4.4, line 1162). This
    rules out degenerate "diagrams" with overlapping or zero-area boxes
    sneaking in through MFS relaxation. -/
theorem counterfactual_sub_WF (P : Program) : ⟦P⟧₊ ⊆ WF := by
  rintro R ⟨M, _, hRM⟩
  exact denotes_sub_WF M hRM

/-- **Soundness.** Every counterfactual realization satisfies *some* MFS
    of `P`. Spytial-core never shows a diagram that fails to realize a
    maximally feasible fragment of the user's spec — there is always a
    coherent constraint subset behind the rendered diagram. -/
theorem counterfactual_witnesses_MFS {P : Program} {R : Realization}
    (hR : R ∈ ⟦P⟧₊) : ∃ M, IsMFS P M ∧ R ∈ denotes M := hR

/-- **Fidelity (SAT case).** When `P` is feasible, the counterfactual
    denotation coincides with the standard denotation: spytial-core
    draws exactly the user's spec, with nothing cut out.

    Paper §5.2 contrast: this is the "happy path" where the system does
    *not* need to take the best-effort/relaxation route. -/
theorem counterfactual_eq_denotes_of_feasible {P : Program}
    (hSat : Feasible P) : ⟦P⟧₊ = denotes P := by
  ext R
  refine ⟨?_, ?_⟩
  · rintro ⟨M, hMFS, hRM⟩
    -- When P is feasible, the only MFS is P itself, so M = P.
    rwa [mfs_unique_of_feasible hSat hMFS] at hRM
  · intro hR
    exact ⟨P, mfs_self_of_feasible hSat, hR⟩

/-- **Totality (UNSAT case).** Even when `P` is unsatisfiable, the
    counterfactual denotation is inhabited (provided `WF.Nonempty`).

    *Why this matters.* This is the formal counterpart of the paper's
    central design claim (§5.2 line 1286-1287): the system can *always*
    show *some* diagram. Counterfactual rendering is a **total**
    function from programs to drawings, in contrast to the
    "reject unsatisfiable layouts" strategy (§5.2 line 1276-1280)
    which is partial. -/
theorem counterfactual_nonempty (P : Program) (hWF : WF.Nonempty) :
    (⟦P⟧₊).Nonempty := by
  obtain ⟨M, hMFS⟩ := mfs_exists P hWF
  obtain ⟨R, hRM⟩ := hMFS.feasible
  exact ⟨R, M, hMFS, hRM⟩

--------------------------------------------------------------------------------
-- 6. The "Cut Out" Set                                  (paper §5.2 "relaxing")
--------------------------------------------------------------------------------

/-- The constraints **dropped** from the rendered diagram: `P` minus the
    chosen MFS. Exactly what `spytial-core`'s qualitative validator
    removes from `layout.constraints` before solving the geometry
    (see `layoutinstance.ts:1424-1425`).

    *Asymmetry from the paper's IIS approach.* Paper §5.2 line 1353
    relaxes a single IIS `I` and renders from `P \ I`. **This is not
    the same as MFS-removal**: `P \ I` is not in general feasible, since
    other IISes in `P` (disjoint from `I` or overlapping but distinct)
    may persist (see `iis_removal_can_remain_infeasible` below).
    MFS-removal is strictly stronger — it yields `M`, which is feasible
    by definition. -/
def droppedConstraints (P M : Program) : Program := P \ M

/-- **Nothing is dropped iff the program is feasible.** A clean
    correspondence between syntax (the drop set) and semantics
    (feasibility of the spec). -/
lemma dropped_empty_iff_feasible {P M : Program} (hMFS : IsMFS P M) :
    droppedConstraints P M = ∅ ↔ Feasible P := by
  unfold droppedConstraints
  refine ⟨fun hEmpty => ?_, fun hSat => ?_⟩
  · -- ⇒  P \ M = ∅ means P ⊆ M; combined with M ⊆ P (MFS), gives M = P,
    --   so M's feasibility is P's feasibility.
    rw [Finset.sdiff_eq_empty_iff_subset] at hEmpty
    have hMP : M = P := Finset.Subset.antisymm hMFS.subset hEmpty
    rw [← hMP]; exact hMFS.feasible
  · -- ⇐  P feasible ⇒ the only MFS is P itself, so M = P and P \ M = ∅.
    rw [mfs_unique_of_feasible hSat hMFS]
    exact Finset.sdiff_self P

--------------------------------------------------------------------------------
-- Worked example: a concrete UNSAT program produces an IIS, an MFS, and
-- a non-empty counterfactual.
--------------------------------------------------------------------------------

/-- **Concrete instance.** A 2-constraint program requiring the same
    nonempty selector `X` to be both `left` and `right` is UNSAT
    (Main.lean's `opposite_orientation_unsat`). Yet our counterfactual
    semantics gives, for this `P`:

    * a witness IIS (via `iis_exists_of_infeasible`),
    * an MFS (via `mfs_exists`), and
    * a non-empty diagram set `⟦P⟧₊` (via `counterfactual_nonempty`).

    This exercises the full API end-to-end on a paper-known UNSAT
    pattern (paper §5.2, "Reporting Unsatisfiable Diagrams"). -/
example (X : Selector₂) (hNE : X.Nonempty) (hWF : WF.Nonempty) :
    let P : Program := {⟨.orientation X .left, .always⟩,
                        ⟨.orientation X .right, .always⟩}
    (∃ I, IsIIS P I) ∧ (∃ M, IsMFS P M) ∧ (⟦P⟧₊).Nonempty := by
  intro P
  -- P is UNSAT by Main.lean's opposite_orientation_unsat.
  have hL : (⟨.orientation X .left, .always⟩ : QualifiedConstraint) ∈ P :=
    Finset.mem_insert_self _ _
  have hR : (⟨.orientation X .right, .always⟩ : QualifiedConstraint) ∈ P :=
    Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  have hEmpty : denotes P = ∅ := opposite_orientation_unsat P X hL hR hNE
  have hUnsat : ¬ Feasible P := by
    unfold Feasible; rw [hEmpty]; exact Set.not_nonempty_empty
  exact ⟨iis_exists_of_infeasible P hUnsat,
         mfs_exists P hWF,
         counterfactual_nonempty P hWF⟩

--------------------------------------------------------------------------------
-- Summary
--------------------------------------------------------------------------------

-- Feasibility (paper §4.4)
#check Feasible                                -- (denotes P).Nonempty
#check empty_feasible_iff                      -- Feasible ∅ ↔ WF.Nonempty

-- IIS — paper §5.1
#check IsIIS                                   -- subset-minimal infeasible
#check iis_exists_of_infeasible                -- ¬Feasible P ⇒ ∃ I, IsIIS P I
#check no_iis_of_feasible                      -- Feasible P ⇒ no IIS
#check unsat_iff_exists_iis                    -- ¬Feasible P ↔ ∃ IIS
#check iis_subset_of_infeasible                -- every infeasible Q ⊆ P contains an IIS

-- MFS — dual of IIS
#check IsMFS                                   -- subset-maximal feasible
#check mfs_exists                              -- under WF.Nonempty, ∃ MFS
#check mfs_self_of_feasible                    -- Feasible P ⇒ P is an MFS
#check mfs_unique_of_feasible                  -- Feasible P ⇒ P is THE MFS

-- Duality & the MFS/IIS asymmetry
#check mfs_hits_every_iis                      -- MFS-complement hits every IIS
#check iis_complement_is_hitting_set           -- restated: I ∩ (P\M) is nonempty
#check mfs_kept_is_feasible                    -- MFS-keeping always yields feasibility
#check iis_removal_can_remain_infeasible       -- IIS-removal does NOT, in general

-- Counterfactual semantics — paper §5.2
#check counterfactual                          -- ⟦P⟧₊
#check counterfactual_sub_WF                   -- ⟦P⟧₊ ⊆ WF
#check counterfactual_witnesses_MFS            -- soundness
#check counterfactual_eq_denotes_of_feasible   -- SAT: ⟦P⟧₊ = ⟦P⟧
#check counterfactual_nonempty                 -- UNSAT: still inhabited (totality)

-- Cut-out set
#check droppedConstraints                      -- P \ M
#check dropped_empty_iff_feasible              -- nothing dropped iff feasible

end Counterfactual
end Spytial
