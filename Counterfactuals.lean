/-
# Counterfactuals.lean — the diagram that Spytial shows for an UNSAT program

When a program has no realization, `spytial-core` still shows a diagram.
It keeps a feasible part of the program and drops the remainder. This
file mechanizes which part it keeps.

## The unit is a diagram-element relation, not a source constraint

`spytial-core` does not keep or drop a source constraint as a whole. It
translates each constraint into **units**. A unit is a list of
**alternatives**, and an alternative is a set of **relations** between
diagram elements ("a is left of b"). A unit holds if one of its
alternatives holds.

| Construct                         | Units                                                       |
|-----------------------------------|-------------------------------------------------------------|
| `orientation`, `align` (always)   | one unit for each pair; one alternative                     |
| `size`, `hideatom` (always)       | one unit for each atom; one alternative                     |
| `cyclic` (always)                 | one unit for each path; one alternative for each offset `k` |
| `orientation`, `align`, `size`, `hideatom` (never) | one unit; one alternative for each pair / atom |
| `group₁`, `group₂` (always, never), `cyclic` (never) | one unit; one alternative (not decomposed) |

`units_correct` proves, for each construct, that the constraint holds iff
all its units hold.

## The construction

`greedy` goes through the units in sequence. For each unit it commits to
the first alternative that is feasible together with the relations kept
until then. If no alternative is feasible, it drops the unit. It does not
go back. This is `computeMaximalFeasibleSubset` in
`qualitative-constraint-validator.ts`.

## Results

* `greedy_feasible` — the kept relations have a realization.
* `greedy_dichotomy` — each unit is kept, or each of its alternatives
  conflicts with the kept relations.
* `kept_constraint_satisfied` — if all units of a constraint are kept,
  the diagram satisfies the constraint. Thus a part of a constraint can
  hold while a different part is dropped (`partial_keep`).
* `greedy_must_isMFS` — if each unit has one alternative, the kept set
  is a Maximal Feasible Subset of the relations. Then the general theory
  applies: each dropped relation is in an IIS (`dropped_in_some_iis`),
  and a relation in no IIS is kept (`uncontested_kept`).
* `feasible_hits_every_iis` — each IIS has a relation that is not kept.
* `commit_not_maximal` — with more than one alternative, the commitment
  can drop a unit that is compatible with the other units. The result is
  maximal for the committed alternatives only.

## Not modeled

* The feasibility check. `greedy` uses the semantic predicate
  `RFeasible`. The implementation uses order graphs.
* The decomposition of group constraints. The group boundary is one
  existential that all members share, so `group₁` and `group₂` stay one
  unit here. The implementation uses one unit for each non-member.
-/

import Main
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Spytial
namespace Counterfactual

--------------------------------------------------------------------------------
-- 1. MFS and IIS for an antimonotone feasibility predicate
--------------------------------------------------------------------------------

section Generic

variable {α : Type*} [DecidableEq α] {Feas : Finset α → Prop}

/-- A subset of a feasible set is feasible. -/
def Antimono (Feas : Finset α → Prop) : Prop :=
  ∀ ⦃S T : Finset α⦄, S ⊆ T → Feas T → Feas S

/-- `I` is an **Irreducible Infeasible Subsystem** of `P`: an infeasible
    subset that becomes feasible when any one element is removed. -/
def IsIIS (Feas : Finset α → Prop) (P I : Finset α) : Prop :=
  I ⊆ P ∧ ¬ Feas I ∧ ∀ c ∈ I, Feas (I.erase c)

/-- `M` is a **Maximal Feasible Subset** of `P`: a feasible subset that
    becomes infeasible when any other element of `P` is added. -/
def IsMFS (Feas : Finset α → Prop) (P M : Finset α) : Prop :=
  M ⊆ P ∧ Feas M ∧ ∀ c ∈ P, c ∉ M → ¬ Feas (insert c M)

/-- Each infeasible subset of `P` contains an IIS of `P`. -/
theorem iis_within {P Q : Finset α} (hQP : Q ⊆ P) (hQ : ¬ Feas Q) :
    ∃ I, IsIIS Feas P I ∧ I ⊆ Q := by
  classical
  have hQ_in : Q ∈ Q.powerset.filter (fun I => ¬ Feas I) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_refl Q, hQ⟩
  obtain ⟨I, hI_mem, hI_min⟩ :=
    Finset.exists_min_image (Q.powerset.filter (fun I => ¬ Feas I))
      Finset.card ⟨Q, hQ_in⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hI_mem
  obtain ⟨hIQ, hIInf⟩ := hI_mem
  refine ⟨I, ⟨hIQ.trans hQP, hIInf, ?_⟩, hIQ⟩
  intro c hcI
  by_contra hErase
  have hErase_in : I.erase c ∈ Q.powerset.filter (fun I => ¬ Feas I) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.erase_subset c I).trans hIQ, hErase⟩
  have hCard := Finset.card_erase_lt_of_mem hcI
  have hLe := hI_min (I.erase c) hErase_in
  omega

/-- A set is infeasible iff it has an IIS. -/
theorem infeasible_iff_exists_iis (hmono : Antimono Feas) (P : Finset α) :
    ¬ Feas P ↔ ∃ I, IsIIS Feas P I := by
  constructor
  · intro h
    obtain ⟨I, hI, _⟩ := iis_within (subset_refl P) h
    exact ⟨I, hI⟩
  · rintro ⟨I, hIP, hInf, _⟩ hF
    exact hInf (hmono hIP hF)

/-- Each feasible subset of `P` is contained in an MFS of `P`. -/
theorem mfs_extends {P Q : Finset α} (hQP : Q ⊆ P) (hQ : Feas Q) :
    ∃ M, IsMFS Feas P M ∧ Q ⊆ M := by
  classical
  have hQ_in : Q ∈ P.powerset.filter (fun M => Q ⊆ M ∧ Feas M) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hQP, subset_refl Q, hQ⟩
  obtain ⟨M, hM_mem, hM_max⟩ :=
    Finset.exists_max_image (P.powerset.filter (fun M => Q ⊆ M ∧ Feas M))
      Finset.card ⟨Q, hQ_in⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hM_mem
  obtain ⟨hMP, hQM, hMFeas⟩ := hM_mem
  refine ⟨M, ⟨hMP, hMFeas, ?_⟩, hQM⟩
  intro c hcP hcM hIns
  have hIns_in :
      insert c M ∈ P.powerset.filter (fun M => Q ⊆ M ∧ Feas M) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset_iff.mpr ⟨hcP, hMP⟩,
           hQM.trans (Finset.subset_insert c M), hIns⟩
  have hCard : M.card < (insert c M).card := by
    rw [Finset.card_insert_of_notMem hcM]; omega
  have hLe := hM_max (insert c M) hIns_in
  omega

/-- If `P` is feasible, its only MFS is `P`. -/
theorem mfs_eq_of_feasible (hmono : Antimono Feas) {P M : Finset α}
    (hP : Feas P) (hM : IsMFS Feas P M) : M = P := by
  by_contra hNe
  obtain ⟨c, hcP, hcM⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hM.1, hNe⟩)
  exact hM.2.2 c hcP hcM (hmono (Finset.insert_subset_iff.mpr ⟨hcP, hM.1⟩) hP)

/-- **Hitting set.** A feasible set does not contain an IIS: each IIS has
    an element outside it. -/
theorem feasible_hits_every_iis (hmono : Antimono Feas) {P K I : Finset α}
    (hK : Feas K) (hI : IsIIS Feas P I) : ∃ c ∈ I, c ∉ K := by
  by_contra hNo
  push_neg at hNo
  exact hI.2.1 (hmono hNo hK)

/-- **Each dropped element is in a conflict.** An element of `P` that is
    not in an MFS is in some IIS of `P`. -/
theorem dropped_in_some_iis (hmono : Antimono Feas) {P M : Finset α} {c : α}
    (hM : IsMFS Feas P M) (hcP : c ∈ P) (hcM : c ∉ M) :
    ∃ I, IsIIS Feas P I ∧ c ∈ I := by
  obtain ⟨I, hI, hIsub⟩ :=
    iis_within (Finset.insert_subset_iff.mpr ⟨hcP, hM.1⟩) (hM.2.2 c hcP hcM)
  refine ⟨I, hI, ?_⟩
  by_contra hcI
  have hIM : I ⊆ M := by
    intro d hd
    rcases Finset.mem_insert.mp (hIsub hd) with hEq | hMem
    · exact absurd (hEq ▸ hd) hcI
    · exact hMem
  exact hI.2.1 (hmono hIM hM.2.1)

/-- **An element in no conflict is kept.** -/
theorem uncontested_kept (hmono : Antimono Feas) {P M : Finset α} {c : α}
    (hM : IsMFS Feas P M) (hcP : c ∈ P)
    (hFree : ∀ I, IsIIS Feas P I → c ∉ I) : c ∈ M := by
  by_contra hcM
  obtain ⟨I, hI, hcI⟩ := dropped_in_some_iis hmono hM hcP hcM
  exact hFree I hI hcI

/-- **The removal of one IIS is not sufficient.** If a second IIS is
    disjoint from the first, the remainder is still infeasible. This is
    why the diagram keeps a feasible set and does not remove one IIS. -/
theorem iis_removal_insufficient (hmono : Antimono Feas) {P I₁ I₂ : Finset α}
    (hI₂ : IsIIS Feas P I₂) (hDisj : Disjoint I₁ I₂) : ¬ Feas (P \ I₁) :=
  fun hF => hI₂.2.1 (hmono
    (fun _ hc => Finset.mem_sdiff.mpr
      ⟨hI₂.1 hc, fun h => Finset.disjoint_left.mp hDisj h hc⟩) hF)

end Generic

--------------------------------------------------------------------------------
-- 2. Diagram-element relations
--------------------------------------------------------------------------------

/-- A relation between diagram elements.

    * `of q` — a constraint on one pair or one atom, for example
      `orientation {(a,b)} right` ("a is left of b").
    * `cyclicAt L k` — the path `L` is on a circle at offset `k`. -/
inductive Rel where
  | of (q : QualifiedConstraint)
  | cyclicAt (L : List Atom) (k : Nat)
deriving DecidableEq

def holds (R : Realization) : Rel → Prop
  | .of q => modelsQC R q
  | .cyclicAt L k => allPairs_ok R L k

/-- The well-formed realizations in which all relations of `K` hold. -/
def relDenotes (K : Finset Rel) : Set Realization :=
  { R | R ∈ WF ∧ ∀ r ∈ K, holds R r }

/-- A set of relations is feasible iff it has a realization. -/
def RFeasible (K : Finset Rel) : Prop := (relDenotes K).Nonempty

lemma rfeasible_mono : Antimono RFeasible :=
  fun _ _ h ⟨R, hWF, hR⟩ => ⟨R, hWF, fun r hr => hR r (h hr)⟩

lemma rfeasible_empty (hWF : WF.Nonempty) : RFeasible ∅ :=
  let ⟨R, hR⟩ := hWF
  ⟨R, hR, fun _ hr => absurd hr (Finset.notMem_empty _)⟩

--------------------------------------------------------------------------------
-- 3. Units: the translation of each construct
--------------------------------------------------------------------------------

/-- A unit: a list of alternatives. Each alternative is a set of
    relations. -/
abbrev DUnit := List (Finset Rel)

/-- A unit holds iff one of its alternatives holds. -/
def modelsU (R : Realization) (u : DUnit) : Prop :=
  ∃ alt ∈ u, ∀ r ∈ alt, holds R r

/-- All relations of `l` are necessary: one unit for each relation. -/
def must (l : List Rel) : List DUnit := l.map (fun r => [{r}])

/-- One relation of `l` is sufficient: one unit, one alternative for
    each relation. -/
def oneOf (l : List Rel) : List DUnit := [l.map (fun r => {r})]

/-- The unit of a cyclic path: one alternative for each offset. -/
def cyclicUnit (L : List Atom) : DUnit :=
  (List.range L.length).map (fun k => {Rel.cyclicAt L k})

/-- The paths of a cyclic constraint that have more than two atoms. -/
noncomputable def cyclicPaths (X : Selector₂) : Rotation → List (List Atom)
  | .clockwise =>
      (maximalSimplePaths X).filter (fun L => 2 < L.length)
  | .counterclockwise =>
      ((maximalSimplePaths X).map List.reverse).filter (fun L => 2 < L.length)

/-- The units of a constraint that must hold. -/
noncomputable def unitsAlways : Constraint → List DUnit
  | .orientation X d =>
      must (X.toList.map fun p => .of ⟨.orientation {p} d, .always⟩)
  | .align X a =>
      must (X.toList.map fun p => .of ⟨.align {p} a, .always⟩)
  | .size w h S =>
      must (S.toList.map fun a => .of ⟨.size w h {a}, .always⟩)
  | .hideatom S =>
      must (S.toList.map fun a => .of ⟨.hideatom {a}, .always⟩)
  | .cyclic X rot => (cyclicPaths X rot).map cyclicUnit
  | .group₁ S => must [.of ⟨.group₁ S, .always⟩]
  | .group₂ X e => must [.of ⟨.group₂ X e, .always⟩]

/-- The units of a constraint that must not hold. The negation of "all
    pairs hold" is "some pair does not hold": one unit with one
    alternative for each pair. -/
noncomputable def unitsNever : Constraint → List DUnit
  | .orientation X d =>
      oneOf (X.toList.map fun p => .of ⟨.orientation {p} d, .never⟩)
  | .align X a =>
      oneOf (X.toList.map fun p => .of ⟨.align {p} a, .never⟩)
  | .size w h S =>
      oneOf (S.toList.map fun a => .of ⟨.size w h {a}, .never⟩)
  | .hideatom S =>
      oneOf (S.toList.map fun a => .of ⟨.hideatom {a}, .never⟩)
  | .cyclic X rot => must [.of ⟨.cyclic X rot, .never⟩]
  | .group₁ S => must [.of ⟨.group₁ S, .never⟩]
  | .group₂ X e => must [.of ⟨.group₂ X e, .never⟩]

/-- The units of a qualified constraint. -/
noncomputable def units : QualifiedConstraint → List DUnit
  | ⟨c, .always⟩ => unitsAlways c
  | ⟨c, .never⟩ => unitsNever c

/-- The units of a program. -/
noncomputable def programUnits (P : Program) : List DUnit :=
  P.toList.flatMap units

/-! ### Each construct holds iff its units hold -/

lemma lift₁_iff_singletons (R : Realization) (S : Selector₁)
    (Pr : Box → Prop) : lift₁ R S Pr ↔ ∀ a ∈ S, lift₁ R {a} Pr := by
  constructor
  · intro h a ha
    unfold lift₁
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact h ha
  · intro h
    unfold lift₁
    intro a ha
    exact h a ha (Finset.mem_singleton_self _)

lemma lift₂_iff_singletons (R : Realization) (X : Selector₂)
    (Pr : Box → Box → Prop) : lift₂ R X Pr ↔ ∀ p ∈ X, lift₂ R {p} Pr := by
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
    (a : AlignDir) : sat_align R X a ↔ ∀ p ∈ X, sat_align R {p} a := by
  cases a <;> exact lift₂_iff_singletons R X _

lemma sat_size_iff_singletons (R : Realization) (w h : PosRat)
    (S : Selector₁) : sat_size R w h S ↔ ∀ a ∈ S, sat_size R w h {a} :=
  lift₁_iff_singletons R S _

lemma sat_hide_iff_singletons (R : Realization) (S : Selector₁) :
    sat_hide R S ↔ ∀ a ∈ S, sat_hide R {a} := by
  simp [sat_hide]

lemma must_iff (R : Realization) (l : List Rel) :
    (∀ u ∈ must l, modelsU R u) ↔ ∀ r ∈ l, holds R r := by
  simp [must, modelsU]

lemma oneOf_iff (R : Realization) (l : List Rel) :
    (∀ u ∈ oneOf l, modelsU R u) ↔ ∃ r ∈ l, holds R r := by
  simp [oneOf, modelsU]

lemma must_toList {β : Type*} (R : Realization) (S : Finset β)
    (f : β → Rel) :
    (∀ u ∈ must (S.toList.map f), modelsU R u) ↔ ∀ x ∈ S, holds R (f x) := by
  rw [must_iff]; simp

lemma oneOf_toList {β : Type*} (R : Realization) (S : Finset β)
    (f : β → Rel) :
    (∀ u ∈ oneOf (S.toList.map f), modelsU R u) ↔ ∃ x ∈ S, holds R (f x) := by
  rw [oneOf_iff]; simp

lemma must_single (R : Realization) (r : Rel) :
    (∀ u ∈ must [r], modelsU R u) ↔ holds R r := by
  rw [must_iff]; simp

lemma not_forall_mem {β : Type*} {S : Finset β} {Q : β → Prop} :
    (¬ ∀ x ∈ S, Q x) ↔ ∃ x ∈ S, ¬ Q x := by
  push_neg; rfl

lemma cyclicUnit_iff (R : Realization) (L : List Atom) :
    modelsU R (cyclicUnit L) ↔ ∃ k, k < L.length ∧ allPairs_ok R L k := by
  simp [cyclicUnit, modelsU, holds]

lemma unitsAlways_correct (R : Realization) (c : Constraint) :
    modelsC R c ↔ ∀ u ∈ unitsAlways c, modelsU R u := by
  cases c with
  | orientation X d =>
    exact (sat_orientation_iff_singletons R X d).trans
      (must_toList R X fun p => .of ⟨.orientation {p} d, .always⟩).symm
  | align X a =>
    exact (sat_align_iff_singletons R X a).trans
      (must_toList R X fun p => .of ⟨.align {p} a, .always⟩).symm
  | size w h S =>
    exact (sat_size_iff_singletons R w h S).trans
      (must_toList R S fun a => .of ⟨.size w h {a}, .always⟩).symm
  | hideatom S =>
    exact (sat_hide_iff_singletons R S).trans
      (must_toList R S fun a => .of ⟨.hideatom {a}, .always⟩).symm
  | group₁ S => exact (must_single R (.of ⟨.group₁ S, .always⟩)).symm
  | group₂ X e => exact (must_single R (.of ⟨.group₂ X e, .always⟩)).symm
  | cyclic X rot =>
    cases rot with
    | clockwise =>
      show (∀ L ∈ maximalSimplePaths X, 2 < L.length →
              ∃ k, k < L.length ∧ allPairs_ok R L k) ↔
           ∀ u ∈ ((maximalSimplePaths X).filter
              (fun L => 2 < L.length)).map cyclicUnit, modelsU R u
      constructor
      · intro h u hu
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hu
        obtain ⟨hLm, hlen⟩ := List.mem_filter.mp hL
        exact (cyclicUnit_iff R L).mpr (h L hLm (of_decide_eq_true hlen))
      · intro h L hLm hlen
        exact (cyclicUnit_iff R L).mp (h _ (List.mem_map.mpr
          ⟨L, List.mem_filter.mpr ⟨hLm, decide_eq_true hlen⟩, rfl⟩))
    | counterclockwise =>
      show (∀ L ∈ maximalSimplePaths X, 2 < L.reverse.length →
              ∃ k, k < L.reverse.length ∧ allPairs_ok R L.reverse k) ↔
           ∀ u ∈ (((maximalSimplePaths X).map List.reverse).filter
              (fun L => 2 < L.length)).map cyclicUnit, modelsU R u
      constructor
      · intro h u hu
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hu
        obtain ⟨hLm, hlen⟩ := List.mem_filter.mp hL
        obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.mp hLm
        exact (cyclicUnit_iff R _).mpr (h L₀ hL₀ (of_decide_eq_true hlen))
      · intro h L hLm hlen
        exact (cyclicUnit_iff R _).mp (h _ (List.mem_map.mpr
          ⟨L.reverse, List.mem_filter.mpr
            ⟨List.mem_map.mpr ⟨L, hLm, rfl⟩, decide_eq_true hlen⟩, rfl⟩))

lemma unitsNever_correct (R : Realization) (c : Constraint) :
    modelsNegC R c ↔ ∀ u ∈ unitsNever c, modelsU R u := by
  cases c with
  | orientation X d =>
    exact ((not_congr (sat_orientation_iff_singletons R X d)).trans
      not_forall_mem).trans
      (oneOf_toList R X fun p => .of ⟨.orientation {p} d, .never⟩).symm
  | align X a =>
    exact ((not_congr (sat_align_iff_singletons R X a)).trans
      not_forall_mem).trans
      (oneOf_toList R X fun p => .of ⟨.align {p} a, .never⟩).symm
  | size w h S =>
    exact ((not_congr (sat_size_iff_singletons R w h S)).trans
      not_forall_mem).trans
      (oneOf_toList R S fun a => .of ⟨.size w h {a}, .never⟩).symm
  | hideatom S =>
    exact ((not_congr (sat_hide_iff_singletons R S)).trans
      not_forall_mem).trans
      (oneOf_toList R S fun a => .of ⟨.hideatom {a}, .never⟩).symm
  | cyclic X rot => exact (must_single R (.of ⟨.cyclic X rot, .never⟩)).symm
  | group₁ S => exact (must_single R (.of ⟨.group₁ S, .never⟩)).symm
  | group₂ X e => exact (must_single R (.of ⟨.group₂ X e, .never⟩)).symm

/-- **The translation is correct for each construct.** A qualified
    constraint holds iff all its units hold. -/
theorem units_correct (R : Realization) (q : QualifiedConstraint) :
    modelsQC R q ↔ ∀ u ∈ units q, modelsU R u := by
  obtain ⟨c, m⟩ := q
  cases m with
  | always => exact unitsAlways_correct R c
  | never => exact unitsNever_correct R c

/-- **The translation keeps the semantics.** The denotation of a program
    is the set of well-formed realizations in which all its units hold. -/
theorem denotes_eq_units (P : Program) :
    denotes P = { R | R ∈ WF ∧ ∀ u ∈ programUnits P, modelsU R u } := by
  ext R
  have h : modelsP R P ↔ ∀ u ∈ programUnits P, modelsU R u := by
    constructor
    · intro h u hu
      obtain ⟨q, hq, huq⟩ := List.mem_flatMap.mp hu
      exact (units_correct R q).mp (h q (Finset.mem_toList.mp hq)) u huq
    · intro h q hq
      exact (units_correct R q).mpr (fun u hu =>
        h u (List.mem_flatMap.mpr ⟨q, Finset.mem_toList.mpr hq, hu⟩))
  simp only [denotes, Set.mem_setOf_eq, h]

--------------------------------------------------------------------------------
-- 4. The greedy construction with committed alternatives
--------------------------------------------------------------------------------

open Classical in
/-- The first alternative of `u` that is feasible together with `acc`. -/
noncomputable def pick (acc : Finset Rel) (u : DUnit) : Option (Finset Rel) :=
  u.find? (fun alt => decide (RFeasible (acc ∪ alt)))

/-- Commit to the picked alternative, or drop the unit. -/
noncomputable def step (acc : Finset Rel) (u : DUnit) : Finset Rel :=
  match pick acc u with
  | some alt => acc ∪ alt
  | none => acc

noncomputable def greedyFrom (acc : Finset Rel) (L : List DUnit) : Finset Rel :=
  L.foldl step acc

/-- **The kept relations.** Go through the units in sequence. For each
    unit, commit to the first alternative that keeps the set feasible. -/
noncomputable def greedy (L : List DUnit) : Finset Rel := greedyFrom ∅ L

/-- `K` keeps the unit `u`: all relations of one alternative are in `K`. -/
def Kept (K : Finset Rel) (u : DUnit) : Prop := ∃ alt ∈ u, alt ⊆ K

lemma step_cases (acc : Finset Rel) (u : DUnit) :
    (∃ alt ∈ u, RFeasible (acc ∪ alt) ∧ step acc u = acc ∪ alt) ∨
    ((∀ alt ∈ u, ¬ RFeasible (acc ∪ alt)) ∧ step acc u = acc) := by
  cases h : pick acc u with
  | some alt =>
    left
    have hs : step acc u = acc ∪ alt := by simp [step, h]
    unfold pick at h
    exact ⟨alt, List.mem_of_find?_eq_some h,
      by simpa using List.find?_some h, hs⟩
  | none =>
    right
    have hs : step acc u = acc := by simp [step, h]
    unfold pick at h
    refine ⟨fun alt halt => ?_, hs⟩
    simpa using List.find?_eq_none.mp h alt halt

lemma subset_step (acc : Finset Rel) (u : DUnit) : acc ⊆ step acc u := by
  rcases step_cases acc u with ⟨alt, _, _, h⟩ | ⟨_, h⟩ <;> rw [h]
  exact Finset.subset_union_left

lemma step_feasible {acc : Finset Rel} (u : DUnit) (h : RFeasible acc) :
    RFeasible (step acc u) := by
  rcases step_cases acc u with ⟨alt, _, hF, hs⟩ | ⟨_, hs⟩ <;> rw [hs]
  · exact hF
  · exact h

lemma greedyFrom_cons (acc : Finset Rel) (u : DUnit) (us : List DUnit) :
    greedyFrom acc (u :: us) = greedyFrom (step acc u) us := rfl

lemma subset_greedyFrom (acc : Finset Rel) (L : List DUnit) :
    acc ⊆ greedyFrom acc L := by
  induction L generalizing acc with
  | nil => exact subset_refl acc
  | cons u us ih =>
    rw [greedyFrom_cons]
    exact (subset_step acc u).trans (ih _)

lemma greedyFrom_feasible {acc : Finset Rel} (L : List DUnit)
    (h : RFeasible acc) : RFeasible (greedyFrom acc L) := by
  induction L generalizing acc with
  | nil => exact h
  | cons u us ih =>
    rw [greedyFrom_cons]
    exact ih (step_feasible u h)

lemma greedyFrom_head (acc : Finset Rel) (u : DUnit) (us : List DUnit) :
    Kept (greedyFrom acc (u :: us)) u ∨
    ∀ alt ∈ u, ¬ RFeasible (greedyFrom acc (u :: us) ∪ alt) := by
  rw [greedyFrom_cons]
  rcases step_cases acc u with ⟨alt, halt, _, hs⟩ | ⟨hnone, _⟩
  · left
    have h : alt ⊆ step acc u := by rw [hs]; exact Finset.subset_union_right
    exact ⟨alt, halt, h.trans (subset_greedyFrom _ _)⟩
  · right
    intro alt halt hF
    exact hnone alt halt (rfeasible_mono
      (Finset.union_subset_union_left
        ((subset_step acc u).trans (subset_greedyFrom _ _))) hF)

lemma greedyFrom_dichotomy (acc : Finset Rel) (L : List DUnit) :
    ∀ u ∈ L, Kept (greedyFrom acc L) u ∨
      ∀ alt ∈ u, ¬ RFeasible (greedyFrom acc L ∪ alt) := by
  induction L generalizing acc with
  | nil => intro u hu; cases hu
  | cons v vs ih =>
    intro u hu
    rcases List.mem_cons.mp hu with huv | hu'
    · rw [huv]; exact greedyFrom_head acc v vs
    · rw [greedyFrom_cons]; exact ih _ u hu'

lemma mem_greedyFrom (acc : Finset Rel) (L : List DUnit) :
    ∀ r ∈ greedyFrom acc L, r ∈ acc ∨ ∃ u ∈ L, ∃ alt ∈ u, r ∈ alt := by
  induction L generalizing acc with
  | nil => intro r hr; exact Or.inl hr
  | cons u us ih =>
    intro r hr
    rw [greedyFrom_cons] at hr
    rcases ih _ r hr with h | ⟨u', hu', alt, halt, hr'⟩
    · rcases step_cases acc u with ⟨alt, halt, _, hs⟩ | ⟨_, hs⟩
      · rw [hs] at h
        rcases Finset.mem_union.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨u, List.mem_cons.mpr (Or.inl rfl), alt, halt, h⟩
      · rw [hs] at h
        exact Or.inl h
    · exact Or.inr ⟨u', List.mem_cons.mpr (Or.inr hu'), alt, halt, hr'⟩

/-- **The kept relations have a realization.** Thus there is always a
    diagram to show. -/
theorem greedy_feasible (L : List DUnit) (hWF : WF.Nonempty) :
    RFeasible (greedy L) :=
  greedyFrom_feasible L (rfeasible_empty hWF)

/-- **Each unit is kept, or all its alternatives are blocked.** If a
    unit is dropped, each of its alternatives conflicts with the kept
    relations. -/
theorem greedy_dichotomy (L : List DUnit) {u : DUnit} (hu : u ∈ L) :
    Kept (greedy L) u ∨ ∀ alt ∈ u, ¬ RFeasible (greedy L ∪ alt) :=
  greedyFrom_dichotomy ∅ L u hu

/-- A kept unit holds in each realization of the kept relations. -/
theorem kept_unit_satisfied {K : Finset Rel} {u : DUnit} (hu : Kept K u)
    {R : Realization} (hR : R ∈ relDenotes K) : modelsU R u :=
  let ⟨alt, halt, hsub⟩ := hu
  ⟨alt, halt, fun r hr => hR.2 r (hsub hr)⟩

/-- **A constraint with all units kept is satisfied.** -/
theorem kept_constraint_satisfied {K : Finset Rel} {q : QualifiedConstraint}
    (hq : ∀ u ∈ units q, Kept K u) {R : Realization}
    (hR : R ∈ relDenotes K) : modelsQC R q :=
  (units_correct R q).mpr (fun u hu => kept_unit_satisfied (hq u hu) hR)

/-- **A violated constraint has a dropped unit.** -/
theorem violated_has_dropped_unit {K : Finset Rel} {q : QualifiedConstraint}
    {R : Realization} (hR : R ∈ relDenotes K) (hViol : ¬ modelsQC R q) :
    ∃ u ∈ units q, ¬ Kept K u := by
  by_contra hNo
  push_neg at hNo
  exact hViol (kept_constraint_satisfied hNo hR)

/-- **With one alternative for each unit, the result is an MFS.** For
    relations that are all necessary (`orientation`, `align`, `size`,
    `hideatom`), the kept set is a Maximal Feasible Subset of the
    relations, for each sequence. -/
theorem greedy_must_isMFS (l : List Rel) (hWF : WF.Nonempty) :
    IsMFS RFeasible l.toFinset (greedy (must l)) := by
  refine ⟨?_, greedy_feasible _ hWF, ?_⟩
  · intro r hr
    rcases mem_greedyFrom ∅ (must l) r hr with h | ⟨u, hu, alt, halt, hr'⟩
    · exact absurd h (Finset.notMem_empty r)
    · obtain ⟨r', hr'l, rfl⟩ := List.mem_map.mp hu
      rw [List.mem_singleton] at halt
      rw [halt, Finset.mem_singleton] at hr'
      rw [hr']
      exact List.mem_toFinset.mpr hr'l
  · intro c hc hcK hF
    have hu : [{c}] ∈ must l :=
      List.mem_map.mpr ⟨c, List.mem_toFinset.mp hc, rfl⟩
    rcases greedy_dichotomy (must l) hu with ⟨alt, halt, hsub⟩ | hBlocked
    · rw [List.mem_singleton] at halt
      rw [halt] at hsub
      exact hcK (hsub (Finset.mem_singleton_self c))
    · refine hBlocked {c} (List.mem_singleton.mpr rfl) (rfeasible_mono ?_ hF)
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
        at hx ⊢
      tauto

--------------------------------------------------------------------------------
-- 5. Two concrete programs
--------------------------------------------------------------------------------

/-- The relation "`a` is left of `b`". -/
def leftOfRel (a b : Atom) : Rel :=
  .of ⟨.orientation {(a, b)} .right, .always⟩

/-- `a` in a unit box at the origin, `b` in a unit box two units to the
    right. All other atoms are hidden. -/
def twoBoxes (a b : Atom) : Realization := fun x =>
  if x = a then some ⟨0, 0, 1, 1, by norm_num, by norm_num⟩
  else if x = b then some ⟨2, 0, 1, 1, by norm_num, by norm_num⟩
  else none

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

lemma leftOfRel_feasible (a b : Atom) (hab : a ≠ b) :
    RFeasible {leftOfRel a b} := by
  refine ⟨twoBoxes a b, twoBoxes_wf a b, fun r hr => ?_⟩
  rw [Finset.mem_singleton] at hr
  rw [hr]
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

lemma leftOf_both_absurd {R : Realization} {a b : Atom}
    (h1 : lift₂ R {(a, b)} leftOf) (h2 : lift₂ R {(b, a)} leftOf) : False := by
  obtain ⟨ba, bb, hba, hbb, hL⟩ := h1 (Finset.mem_singleton_self _)
  obtain ⟨bb', ba', hbb', hba', hR⟩ := h2 (Finset.mem_singleton_self _)
  rw [hba] at hba'; cases hba'
  rw [hbb] at hbb'; cases hbb'
  exact leftOf_asymm (le_of_lt ba.width_pos) (le_of_lt bb.width_pos) hL hR

lemma leftOfRel_both_infeasible (a b : Atom) :
    ¬ RFeasible {leftOfRel a b, leftOfRel b a} := by
  rintro ⟨R, _, hR⟩
  exact leftOf_both_absurd
    (hR (leftOfRel a b) (by simp)) (hR (leftOfRel b a) (by simp))

/-- **A part is kept, a part is dropped.** Let the program be the one
    constraint "`a` is left of `b` and `b` is left of `a`", with `a ≠ b`.
    Its units are the two relations `leftOfRel a b` and `leftOfRel b a`.

    * With the source constraint as the unit, the only MFS is empty: the
      diagram shows nothing of the constraint.
    * With the relation as the unit, each MFS keeps one relation and
      drops the other. -/
theorem partial_keep (a b : Atom) (hab : a ≠ b) :
    (∀ M, IsMFS (fun P : Program => (denotes P).Nonempty)
        {⟨.orientation {(a, b), (b, a)} .right, .always⟩} M → M = ∅) ∧
    (∀ D, IsMFS RFeasible {leftOfRel a b, leftOfRel b a} D →
        D.Nonempty ∧ D ≠ {leftOfRel a b, leftOfRel b a}) := by
  refine ⟨?_, ?_⟩
  · intro M hM
    rcases Finset.subset_singleton_iff.mp hM.1 with h | h
    · exact h
    · exfalso
      obtain ⟨R, _, hSat⟩ := hM.2.1
      rw [h] at hSat
      have hq : lift₂ R {(a, b), (b, a)} leftOf :=
        hSat _ (Finset.mem_singleton_self _)
      have hp := (lift₂_iff_singletons R _ leftOf).mp hq
      exact leftOf_both_absurd (hp (a, b) (by simp)) (hp (b, a) (by simp))
  · intro D hD
    refine ⟨?_, fun h => leftOfRel_both_infeasible a b (h ▸ hD.2.1)⟩
    by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    have hMax := hD.2.2 (leftOfRel a b) (by simp)
      (by rw [hEmpty]; exact Finset.notMem_empty _)
    rw [hEmpty] at hMax
    exact hMax (by simpa using leftOfRel_feasible a b hab)

/-- **The commitment is not maximal.** The first unit has two
    alternatives: "`a` is left of `b`" or "`b` is left of `a`". The
    second unit has one: "`b` is left of `a`". The greedy pass commits to
    the first alternative of the first unit, and then it must drop the
    second unit. But the two units can hold together. -/
theorem commit_not_maximal (a b : Atom) (hab : a ≠ b) :
    greedy [[{leftOfRel a b}, {leftOfRel b a}], [{leftOfRel b a}]]
      = {leftOfRel a b} ∧
    ∃ R ∈ WF, modelsU R [{leftOfRel a b}, {leftOfRel b a}] ∧
              modelsU R [{leftOfRel b a}] := by
  refine ⟨?_, ?_⟩
  · have hA : RFeasible (∅ ∪ {leftOfRel a b}) := by
      simpa using leftOfRel_feasible a b hab
    have hAB : ¬ RFeasible ({leftOfRel a b} ∪ {leftOfRel b a}) := by
      rw [← Finset.insert_eq]; exact leftOfRel_both_infeasible a b
    have h1 : step ∅ [{leftOfRel a b}, {leftOfRel b a}] = {leftOfRel a b} := by
      have hp : pick ∅ [{leftOfRel a b}, {leftOfRel b a}]
          = some {leftOfRel a b} := by
        unfold pick
        exact List.find?_cons_of_pos (by simpa using hA)
      simp [step, hp]
    have h2 : step {leftOfRel a b} [{leftOfRel b a}] = {leftOfRel a b} := by
      rcases step_cases {leftOfRel a b} [{leftOfRel b a}] with
        ⟨alt, halt, hF, _⟩ | ⟨_, hs⟩
      · rw [List.mem_singleton] at halt
        rw [halt] at hF
        exact absurd hF hAB
      · exact hs
    show step (step ∅ _) _ = _
    rw [h1, h2]
  · obtain ⟨R, hWF, hR⟩ := leftOfRel_feasible b a hab.symm
    exact ⟨R, hWF, ⟨{leftOfRel b a}, by simp, hR⟩, ⟨{leftOfRel b a}, by simp, hR⟩⟩

end Counterfactual
end Spytial
