/-
# DiagramMFS.lean — the MFS at the diagram-element level

`Counterfactuals.lean` defines the Maximal Feasible Subset (MFS) with the
**source constraint** as the unit: `orientation X left` is kept or dropped
as a whole.

`spytial-core` does not do this. Its qualitative validator
(`computeMaximalFeasibleSubset` in `qualitative-constraint-validator.ts`)
keeps or drops **diagram-element relations**: one `LeftConstraint`,
`TopConstraint` or `AlignmentConstraint` between two nodes. Thus one part
of a source constraint can be kept while a different part is dropped.

This file makes the mechanization agree with that construction.

## The idea

A diagram-element relation "a is left of b" is the source constraint
`orientation {(a,b)} left` — the same constraint with a singleton
selector. So we do not need a new type. We **atomize** a program:

    atomize P  :=  each `always` orientation / align constraint on a
                   selector X is replaced by one constraint for each
                   pair of X; all other constraints stay as one unit.

`denotes_atomize` proves `⟦atomize P⟧ = ⟦P⟧`. The diagram-level MFS is
then only `IsMFS (atomize P) D`, and **every theorem of
`Counterfactuals.lean` applies to it without change**.

## What this file proves

| Theorem                         | Statement                                                              |
|---------------------------------|------------------------------------------------------------------------|
| `denotes_atomize`               | `⟦atomize P⟧ = ⟦P⟧`                                                    |
| `mfs_extends`                   | each feasible subset is in some MFS                                    |
| `diagramMFS_exists`             | a diagram-level MFS exists (if `WF` is not empty)                      |
| `diagramMFS_refines`            | each constraint-level MFS `M` has a diagram-level MFS `D ⊇ atomize M`, with `⟦D⟧ ⊆ ⟦M⟧` |
| `diagramMFS_eq_of_feasible`     | SAT case: `⟦D⟧ = ⟦P⟧`                                                  |
| `fully_kept_is_satisfied`       | a constraint with all atoms kept is satisfied by the diagram           |
| `violated_has_dropped_atom`     | a constraint that the diagram violates has a dropped atom              |
| `dropped_atom_in_conflict`      | each dropped atom is in some diagram-level IIS                         |
| `uncontested_atom_kept`         | an atom in no IIS is in every diagram-level MFS                        |
| `diagramMFS_hits_every_iis`     | each diagram-level IIS has a dropped atom                              |
| `greedy_isMFS`                  | the greedy pass (the implementation's algorithm) gives an MFS          |
| `greedy_isDiagramMFS`           | the greedy pass on the atoms gives a diagram-level MFS                 |
| `greedy_keeps_head`             | the first relation in the sequence is kept if it is feasible alone     |
| `partial_keep_witness`          | a concrete program where the constraint-level MFS is empty, but each diagram-level MFS keeps a part of the constraint |

## What this file does not model

* **Disjunctive units.** `cyclic`, group and `never` constraints stay one
  unit in `atomize`. The implementation commits to one alternative of
  each disjunction and does not go back. That commitment is not modeled
  here, so `greedy_isMFS` describes the conjunctive pass only.
* **Feasibility check.** `greedyFrom` uses the semantic predicate
  `Feasible`. The implementation uses order graphs. The relation between
  the two is the subject of `AbstractSolver.lean`.
-/

import Counterfactuals

namespace Spytial
namespace DiagramLevel

open Counterfactual

--------------------------------------------------------------------------------
-- 1. Atoms: diagram-element relations as singleton-selector constraints
--------------------------------------------------------------------------------

/-- A pairwise-lifted relation holds on a selector iff it holds on each
    pair of the selector separately. This is why orientation and
    alignment constraints decompose into diagram-element relations. -/
lemma lift₂_iff_singletons (R : Realization) (X : Selector₂)
    (Pr : Box → Box → Prop) :
    lift₂ R X Pr ↔ ∀ p ∈ X, lift₂ R {p} Pr := by
  constructor
  · intro h p hp
    unfold lift₂
    intro a b hab
    rw [Finset.mem_singleton] at hab
    subst hab
    exact h hp
  · intro h
    unfold lift₂
    intro a b hab
    exact h (a, b) hab (Finset.mem_singleton_self _)

lemma sat_orientation_iff_singletons (R : Realization) (X : Selector₂)
    (d : Direction) :
    sat_orientation R X d ↔ ∀ p ∈ X, sat_orientation R {p} d := by
  cases d <;> exact lift₂_iff_singletons R X _

lemma sat_align_iff_singletons (R : Realization) (X : Selector₂)
    (a : AlignDir) :
    sat_align R X a ↔ ∀ p ∈ X, sat_align R {p} a := by
  cases a <;> exact lift₂_iff_singletons R X _

/-- The diagram-element relations of one (positive) constraint.
    Orientation and alignment split into one relation for each pair.
    All other constraints are one unit. -/
def atomsC : Constraint → Finset Constraint
  | .orientation X d => X.image (fun p => Constraint.orientation {p} d)
  | .align X a       => X.image (fun p => Constraint.align {p} a)
  | c                => {c}

/-- The diagram-element relations of a qualified constraint. A `never`
    constraint is one unit: its negation is a disjunction over the pairs,
    not a conjunction, so it does not split. -/
def atoms : QualifiedConstraint → Program
  | ⟨c, .always⟩ => (atomsC c).image (fun c' => ⟨c', .always⟩)
  | ⟨c, .never⟩  => {⟨c, .never⟩}

/-- The diagram-level program: all diagram-element relations of `P`. -/
def atomize (P : Program) : Program := P.biUnion atoms

lemma modelsC_iff_atomsC (R : Realization) (c : Constraint) :
    modelsC R c ↔ ∀ c' ∈ atomsC c, modelsC R c' := by
  cases c with
  | orientation X d =>
    constructor
    · intro h c' hc'
      simp only [atomsC, Finset.mem_image] at hc'
      obtain ⟨p, hp, rfl⟩ := hc'
      exact (sat_orientation_iff_singletons R X d).mp h p hp
    · intro h
      refine (sat_orientation_iff_singletons R X d).mpr (fun p hp => ?_)
      exact h _ (by simp only [atomsC, Finset.mem_image]; exact ⟨p, hp, rfl⟩)
  | align X a =>
    constructor
    · intro h c' hc'
      simp only [atomsC, Finset.mem_image] at hc'
      obtain ⟨p, hp, rfl⟩ := hc'
      exact (sat_align_iff_singletons R X a).mp h p hp
    · intro h
      refine (sat_align_iff_singletons R X a).mpr (fun p hp => ?_)
      exact h _ (by simp only [atomsC, Finset.mem_image]; exact ⟨p, hp, rfl⟩)
  | _ => simp [atomsC]

/-- A constraint holds iff all its diagram-element relations hold. -/
lemma modelsQC_iff_atoms (R : Realization) (q : QualifiedConstraint) :
    modelsQC R q ↔ ∀ r ∈ atoms q, modelsQC R r := by
  obtain ⟨c, m⟩ := q
  cases m with
  | always =>
    constructor
    · intro h r hr
      simp only [atoms, Finset.mem_image] at hr
      obtain ⟨c', hc', rfl⟩ := hr
      exact (modelsC_iff_atomsC R c).mp h c' hc'
    · intro h
      refine (modelsC_iff_atomsC R c).mpr (fun c' hc' => ?_)
      exact h ⟨c', .always⟩
        (by simp only [atoms, Finset.mem_image]; exact ⟨c', hc', rfl⟩)
  | never => simp [atoms]

lemma modelsP_atomize (R : Realization) (P : Program) :
    modelsP R (atomize P) ↔ modelsP R P := by
  constructor
  · intro h q hq
    exact (modelsQC_iff_atoms R q).mpr
      (fun r hr => h r (Finset.mem_biUnion.mpr ⟨q, hq, hr⟩))
  · intro h r hr
    obtain ⟨q, hq, hrq⟩ := Finset.mem_biUnion.mp hr
    exact (modelsQC_iff_atoms R q).mp (h q hq) r hrq

/-- **Atomization preserves the semantics.** The diagram-level program
    has the same denotation as the source program. -/
theorem denotes_atomize (P : Program) : denotes (atomize P) = denotes P := by
  ext R
  unfold denotes
  simp only [Set.mem_setOf_eq, modelsP_atomize]

theorem feasible_atomize (P : Program) :
    Feasible (atomize P) ↔ Feasible P := by
  unfold Feasible
  rw [denotes_atomize]

lemma atomize_mono {P Q : Program} (h : P ⊆ Q) : atomize P ⊆ atomize Q :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma atoms_subset_atomize {P : Program} {q : QualifiedConstraint}
    (hq : q ∈ P) : atoms q ⊆ atomize P :=
  fun _ hr => Finset.mem_biUnion.mpr ⟨q, hq, hr⟩

--------------------------------------------------------------------------------
-- 2. A general MFS fact: each feasible subset extends to an MFS
--------------------------------------------------------------------------------

/-- Each feasible subset of `P` is contained in some MFS of `P`. -/
theorem mfs_extends {P Q : Program} (hQP : Q ⊆ P) (hQ : Feasible Q) :
    ∃ M, IsMFS P M ∧ Q ⊆ M := by
  classical
  have hQ_in :
      Q ∈ P.powerset.filter (fun M => Q ⊆ M ∧ (denotes M).Nonempty) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hQP, subset_refl Q, hQ⟩
  obtain ⟨M, hM_mem, hM_max⟩ :=
    Finset.exists_max_image
      (P.powerset.filter (fun M => Q ⊆ M ∧ (denotes M).Nonempty))
      Finset.card ⟨Q, hQ_in⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hM_mem
  obtain ⟨hMP, hQM, hMFeas⟩ := hM_mem
  refine ⟨M, ⟨hMP, hMFeas, ?_⟩, hQM⟩
  intro c hcP hcM hFeasIns
  have hIns :
      insert c M ∈
        P.powerset.filter (fun M => Q ⊆ M ∧ (denotes M).Nonempty) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset_iff.mpr ⟨hcP, hMP⟩,
           hQM.trans (Finset.subset_insert c M), hFeasIns⟩
  have hCard : M.card < (insert c M).card := by
    rw [Finset.card_insert_of_notMem hcM]; omega
  have h_le := hM_max (insert c M) hIns
  omega

--------------------------------------------------------------------------------
-- 3. The diagram-level MFS and IIS
--------------------------------------------------------------------------------

/-- `D` is a **diagram-level MFS** of `P`: a maximal feasible set of
    diagram-element relations of `P`. This is the object that
    `spytial-core` constructs. -/
def IsDiagramMFS (P D : Program) : Prop := IsMFS (atomize P) D

/-- `I` is a **diagram-level IIS** of `P`: a minimal infeasible set of
    diagram-element relations of `P`. -/
def IsDiagramIIS (P I : Program) : Prop := IsIIS (atomize P) I

theorem diagramMFS_exists (P : Program) (hWF : WF.Nonempty) :
    ∃ D, IsDiagramMFS P D :=
  mfs_exists (atomize P) hWF

/-- **Refinement.** The diagram level keeps no less than the constraint
    level. For each constraint-level MFS `M` there is a diagram-level
    MFS `D` that contains all relations of `M`. Each realization of `D`
    is a realization of `M`. -/
theorem diagramMFS_refines {P M : Program} (hM : IsMFS P M) :
    ∃ D, IsDiagramMFS P D ∧ atomize M ⊆ D ∧ denotes D ⊆ denotes M := by
  obtain ⟨D, hD, hsub⟩ :=
    mfs_extends (atomize_mono hM.subset) ((feasible_atomize M).mpr hM.feasible)
  refine ⟨D, hD, hsub, ?_⟩
  have h := antimonotonicity hsub
  rwa [denotes_atomize] at h

/-- **Fidelity (SAT case).** If `P` is feasible, the diagram-level MFS
    has the denotation of `P`. Nothing is dropped. -/
theorem diagramMFS_eq_of_feasible {P D : Program} (hSat : Feasible P)
    (hD : IsDiagramMFS P D) : denotes D = denotes P := by
  have hDeq : D = atomize P :=
    mfs_unique_of_feasible ((feasible_atomize P).mpr hSat) hD
  rw [hDeq, denotes_atomize]

/-- **Fully kept ⇒ satisfied.** If all relations of a constraint are in
    `D`, each realization of `D` satisfies the constraint. -/
theorem fully_kept_is_satisfied {D : Program} {q : QualifiedConstraint}
    (hq : atoms q ⊆ D) {R : Realization} (hR : R ∈ denotes D) : modelsQC R q :=
  (modelsQC_iff_atoms R q).mpr (fun r hr => hR.2 r (hq hr))

/-- The source constraints that the diagram keeps fully. -/
def fullyKept (P D : Program) : Program := by
  classical exact P.filter (fun q => atoms q ⊆ D)

/-- The diagram satisfies each fully kept source constraint. -/
theorem denotes_sub_fullyKept (P D : Program) : denotes D ⊆ denotes (fullyKept P D) := by
  classical
  intro R hR
  refine ⟨hR.1, fun q hq => ?_⟩
  have hq' : atoms q ⊆ D := by
    unfold fullyKept at hq
    exact (Finset.mem_filter.mp hq).2
  exact fully_kept_is_satisfied hq' hR

/-- **Violated ⇒ some relation dropped.** If a realization of `D` does
    not satisfy `q`, then `D` does not contain some relation of `q`. -/
theorem violated_has_dropped_atom {D : Program} {q : QualifiedConstraint}
    {R : Realization} (hR : R ∈ denotes D) (hViol : ¬ modelsQC R q) :
    ∃ r ∈ atoms q, r ∉ D := by
  by_contra hNo
  push_neg at hNo
  exact hViol (fully_kept_is_satisfied hNo hR)

/-- **Each dropped relation is in a conflict.** -/
theorem dropped_atom_in_conflict {P D : Program} (hD : IsDiagramMFS P D)
    {r : QualifiedConstraint} (hr : r ∈ atomize P \ D) :
    ∃ I, IsDiagramIIS P I ∧ r ∈ I :=
  dropped_belongs_to_some_iis hD hr

/-- **A relation in no conflict is always kept.** If a diagram-element
    relation is in no diagram-level IIS, it is in every diagram-level
    MFS. At the constraint level this is false for the relation: the
    full source constraint is dropped when one of its pairs conflicts. -/
theorem uncontested_atom_kept {P D : Program} (hD : IsDiagramMFS P D)
    {r : QualifiedConstraint} (hr : r ∈ atomize P)
    (hFree : ∀ I, IsDiagramIIS P I → r ∉ I) : r ∈ D := by
  by_contra hrD
  obtain ⟨I, hI, hrI⟩ :=
    dropped_atom_in_conflict hD (Finset.mem_sdiff.mpr ⟨hr, hrD⟩)
  exact hFree I hI hrI

/-- **Hitting set.** Each diagram-level IIS has a dropped relation. -/
theorem diagramMFS_hits_every_iis {P D I : Program}
    (hD : IsDiagramMFS P D) (hI : IsDiagramIIS P I) : ∃ r ∈ I, r ∉ D :=
  mfs_hits_every_iis hD hI

--------------------------------------------------------------------------------
-- 4. The greedy construction (the implementation's algorithm)
--------------------------------------------------------------------------------

open Classical in
/-- The greedy pass. Go through the relations in sequence. Keep a
    relation iff the kept set stays feasible. This is the conjunctive
    loop of `computeMaximalFeasibleSubset` in `spytial-core`. -/
noncomputable def greedyFrom (acc : Program) :
    List QualifiedConstraint → Program
  | [] => acc
  | c :: cs =>
    if Feasible (insert c acc) then greedyFrom (insert c acc) cs
    else greedyFrom acc cs

lemma greedyFrom_acc_subset (acc : Program) (L : List QualifiedConstraint) :
    acc ⊆ greedyFrom acc L := by
  induction L generalizing acc with
  | nil => simp [greedyFrom]
  | cons c cs ih =>
    simp only [greedyFrom]
    split_ifs
    · exact (Finset.subset_insert c acc).trans (ih _)
    · exact ih _

lemma greedyFrom_subset_input (acc : Program)
    (L : List QualifiedConstraint) :
    greedyFrom acc L ⊆ acc ∪ L.toFinset := by
  induction L generalizing acc with
  | nil => simp [greedyFrom]
  | cons c cs ih =>
    simp only [greedyFrom]
    split_ifs
    · refine (ih _).trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
        List.mem_cons] at hx ⊢
      tauto
    · refine (ih _).trans ?_
      intro x hx
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at hx ⊢
      tauto

lemma greedyFrom_feasible (acc : Program) (L : List QualifiedConstraint)
    (hacc : Feasible acc) : Feasible (greedyFrom acc L) := by
  induction L generalizing acc with
  | nil => simpa [greedyFrom] using hacc
  | cons c cs ih =>
    simp only [greedyFrom]
    split_ifs with h
    · exact ih _ h
    · exact ih _ hacc

lemma greedyFrom_maximal (acc : Program) (L : List QualifiedConstraint) :
    ∀ c ∈ L, c ∉ greedyFrom acc L →
      ¬ Feasible (insert c (greedyFrom acc L)) := by
  induction L generalizing acc with
  | nil => intro c hc; cases hc
  | cons d ds ih =>
    intro c hc hnot
    simp only [greedyFrom] at hnot ⊢
    split_ifs at hnot ⊢ with h
    · rcases List.mem_cons.mp hc with hcd | hc'
      · subst hcd
        exact absurd
          (greedyFrom_acc_subset _ _ (Finset.mem_insert_self _ _)) hnot
      · exact ih _ c hc' hnot
    · rcases List.mem_cons.mp hc with hcd | hc'
      · subst hcd
        intro hf
        exact h (feasible_of_subset
          (Finset.insert_subset_insert _ (greedyFrom_acc_subset _ _)) hf)
      · exact ih _ c hc' hnot

/-- **The greedy pass gives an MFS.** For each sequence of the
    constraints, the kept set is a maximal feasible subset. The proof is
    constructive in the algorithm: a rejected relation conflicts with
    relations that are kept at that time, and those relations stay. -/
theorem greedy_isMFS (L : List QualifiedConstraint) (hWF : WF.Nonempty) :
    IsMFS L.toFinset (greedyFrom ∅ L) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := greedyFrom_subset_input ∅ L
    rwa [Finset.empty_union] at h
  · exact greedyFrom_feasible _ _ (empty_feasible_iff.mpr hWF)
  · intro c hc hnot
    exact greedyFrom_maximal ∅ L c (List.mem_toFinset.mp hc) hnot

/-- **The greedy pass on the diagram-element relations gives a
    diagram-level MFS.** `L` is a sequence of all relations of `P`. -/
theorem greedy_isDiagramMFS (P : Program) (L : List QualifiedConstraint)
    (hL : L.toFinset = atomize P) (hWF : WF.Nonempty) :
    IsDiagramMFS P (greedyFrom ∅ L) := by
  unfold IsDiagramMFS
  rw [← hL]
  exact greedy_isMFS L hWF

/-- **The sequence gives the priority.** The first relation is kept if
    it is feasible by itself. Thus the result of the greedy pass depends
    on the sequence, and a different sequence can give a different MFS. -/
theorem greedy_keeps_head (c : QualifiedConstraint)
    (cs : List QualifiedConstraint) (h : Feasible {c}) :
    c ∈ greedyFrom ∅ (c :: cs) := by
  have h' : Feasible (insert c (∅ : Program)) := by simpa using h
  simp only [greedyFrom, if_pos h']
  exact greedyFrom_acc_subset _ _ (Finset.mem_insert_self _ _)

--------------------------------------------------------------------------------
-- 5. A concrete program: a part is kept, a part is dropped
--------------------------------------------------------------------------------

/-- A realization with `a` in a unit box at the origin and `b` in a unit
    box two units to the right. All other atoms are hidden. -/
def twoBoxes (a b : Atom) : Realization := fun x =>
  if x = a then some ⟨0, 0, 1, 1, by norm_num, by norm_num⟩
  else if x = b then some ⟨2, 0, 1, 1, by norm_num, by norm_num⟩
  else none

/-- Each visible atom of `twoBoxes` is `a` (at x = 0) or `b` (at x = 2). -/
lemma twoBoxes_some (a b x : Atom) (bx : Box) (h : twoBoxes a b x = some bx) :
    (x = a ∧ bx.x_tl = 0 ∧ bx.width = 1) ∨
    (x = b ∧ bx.x_tl = 2 ∧ bx.width = 1) := by
  unfold twoBoxes at h
  split_ifs at h <;>
    first
      | (left; cases h; exact ⟨‹x = a›, rfl, rfl⟩)
      | (right; cases h; exact ⟨‹x = b›, rfl, rfl⟩)

lemma twoBoxes_wf (a b : Atom) : twoBoxes a b ∈ WF := by
  refine ⟨fun _ bx _ => ⟨bx.width_pos, bx.height_pos⟩, ?_, ?_⟩
  · intro a₁ a₂ b₁ b₂ hne h1 h2
    rcases twoBoxes_some a b a₁ b₁ h1 with ⟨e1, x1, w1⟩ | ⟨e1, x1, w1⟩ <;>
    rcases twoBoxes_some a b a₂ b₂ h2 with ⟨e2, x2, w2⟩ | ⟨e2, x2, w2⟩
    · exact absurd (e1.trans e2.symm) hne
    · intro h
      obtain ⟨⟨_, h'⟩, _⟩ := h
      linarith
    · intro h
      obtain ⟨⟨h', _⟩, _⟩ := h
      linarith
    · exact absurd (e1.trans e2.symm) hne
  · intro a₁ a₂ bx hne h1 h2
    rcases twoBoxes_some a b a₁ bx h1 with ⟨e1, x1, _⟩ | ⟨e1, x1, _⟩ <;>
    rcases twoBoxes_some a b a₂ bx h2 with ⟨e2, x2, _⟩ | ⟨e2, x2, _⟩
    · exact absurd (e1.trans e2.symm) hne
    · linarith
    · linarith
    · exact absurd (e1.trans e2.symm) hne

/-- The relation "`a` is left of `b`" alone is feasible. -/
lemma right_pair_feasible (a b : Atom) (hab : a ≠ b) :
    Feasible {(⟨.orientation {(a, b)} .right, .always⟩ : QualifiedConstraint)} := by
  refine ⟨twoBoxes a b, twoBoxes_wf a b, ?_⟩
  intro c hc
  rw [Finset.mem_singleton] at hc
  subst hc
  show lift₂ (twoBoxes a b) {(a, b)} leftOf
  unfold lift₂
  intro x y hxy
  rw [Finset.mem_singleton, Prod.mk.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  refine ⟨⟨0, 0, 1, 1, by norm_num, by norm_num⟩,
          ⟨2, 0, 1, 1, by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
  · simp [twoBoxes]
  · simp [twoBoxes, hab.symm]
  · simp [leftOf]

/-- The constraint "`a` is left of `b` **and** `b` is left of `a`" is
    infeasible. -/
lemma right_both_infeasible (a b : Atom) :
    ¬ Feasible {(⟨.orientation {(a, b), (b, a)} .right, .always⟩ :
      QualifiedConstraint)} := by
  rintro ⟨R, _, hSat⟩
  have h : lift₂ R {(a, b), (b, a)} leftOf :=
    hSat _ (Finset.mem_singleton_self _)
  obtain ⟨ba, bb, hba, hbb, hL⟩ :=
    h (show (a, b) ∈ ({(a, b), (b, a)} : Selector₂) by simp)
  obtain ⟨bb', ba', hbb', hba', hR⟩ :=
    h (show (b, a) ∈ ({(a, b), (b, a)} : Selector₂) by simp)
  rw [hba] at hba'; cases hba'
  rw [hbb] at hbb'; cases hbb'
  exact leftOf_asymm (le_of_lt ba.width_pos) (le_of_lt bb.width_pos) hL hR

/-- **A part is kept, a part is dropped.** Let `P` be the one constraint
    "`a` is left of `b` and `b` is left of `a`", with `a ≠ b`.

    * At the **constraint level**, the only MFS is empty. The diagram
      shows nothing of the constraint.
    * At the **diagram level**, each MFS keeps a part of the constraint
      and drops a part of it.

    This is the property of `spytial-core` that the constraint-level
    definition cannot express. -/
theorem partial_keep_witness (a b : Atom) (hab : a ≠ b) :
    let q : QualifiedConstraint :=
      ⟨.orientation {(a, b), (b, a)} .right, .always⟩
    let P : Program := {q}
    (∀ M, IsMFS P M → M = ∅) ∧
    (∀ D, IsDiagramMFS P D → (atoms q ∩ D).Nonempty ∧ ¬ atoms q ⊆ D) := by
  intro q P
  have hInf : ¬ Feasible P := right_both_infeasible a b
  have hAt : atomize P = atoms q := Finset.singleton_biUnion
  refine ⟨?_, ?_⟩
  · intro M hM
    rcases Finset.subset_singleton_iff.mp hM.subset with h | h
    · exact h
    · have hF : Feasible P := by
        have hMf := hM.feasible
        rwa [h] at hMf
      exact absurd hF hInf
  · intro D hD
    have hDsub : D ⊆ atoms q := by
      have h := hD.subset
      rwa [hAt] at h
    have hNotAll : ¬ atoms q ⊆ D := by
      intro hsub
      have hEq : D = atomize P := by
        rw [hAt]; exact Finset.Subset.antisymm hDsub hsub
      have hF : Feasible (atomize P) := by
        rw [← hEq]; exact hD.feasible
      exact hInf ((feasible_atomize P).mp hF)
    refine ⟨?_, hNotAll⟩
    by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    -- No relation of `q` is in `D`, and `D ⊆ atoms q`, so `D = ∅`.
    have hD0 : D = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro r hr
      have : r ∈ atoms q ∩ D := Finset.mem_inter.mpr ⟨hDsub hr, hr⟩
      rw [hEmpty] at this
      exact absurd this (Finset.notMem_empty r)
    -- But "a left of b" is a relation of `q` and is feasible alone.
    let r : QualifiedConstraint := ⟨.orientation {(a, b)} .right, .always⟩
    have hrq : r ∈ atoms q := by
      simp only [q, r, atoms, atomsC, Finset.mem_image]
      exact ⟨_, ⟨(a, b), by simp, rfl⟩, rfl⟩
    have hrD : r ∉ D := by rw [hD0]; exact Finset.notMem_empty r
    have hrP : r ∈ atomize P := by rw [hAt]; exact hrq
    have hMax := hD.maximal r hrP hrD
    rw [hD0] at hMax
    exact hMax (by simpa using right_pair_feasible a b hab)

--------------------------------------------------------------------------------
-- Summary
--------------------------------------------------------------------------------

-- Atomization
#check denotes_atomize            -- ⟦atomize P⟧ = ⟦P⟧
#check feasible_atomize           -- Feasible (atomize P) ↔ Feasible P

-- Diagram-level MFS
#check IsDiagramMFS               -- IsMFS (atomize P) D
#check diagramMFS_exists          -- exists if WF is not empty
#check diagramMFS_refines         -- keeps no less than the constraint level
#check diagramMFS_eq_of_feasible  -- SAT: ⟦D⟧ = ⟦P⟧
#check fully_kept_is_satisfied    -- all atoms kept ⇒ constraint satisfied
#check denotes_sub_fullyKept      -- ⟦D⟧ ⊆ ⟦fullyKept P D⟧
#check violated_has_dropped_atom  -- violated ⇒ an atom is dropped
#check dropped_atom_in_conflict   -- each dropped atom is in an IIS
#check uncontested_atom_kept      -- an atom in no IIS is always kept
#check diagramMFS_hits_every_iis  -- each IIS has a dropped atom

-- Greedy construction
#check greedy_isMFS               -- the greedy pass gives an MFS
#check greedy_isDiagramMFS        -- ... at the diagram level
#check greedy_keeps_head          -- the sequence gives the priority

-- Concrete program
#check partial_keep_witness       -- a part kept, a part dropped

end DiagramLevel
end Spytial
