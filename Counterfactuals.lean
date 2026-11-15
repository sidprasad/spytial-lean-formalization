/-
# Counterfactual diagrams

When the source rules conflict, the counterfactual diagram keeps a feasible subset
of the diagram-element relations: left of, above, vertically aligned, or horizontally aligned.
An alternative is a conjunction of these relations. A disjunction is a list of alternatives
from which the diagram may take one. For example, `directlyRight` on (a, b)
emits two independent constraints, while all the pair relations of one cyclic rotation
belong to a single alternative.

`translate?` translates orientation, alignment, and cyclic rules. Size, hiding, and
group boundaries have separate source semantics in Main; translating groups to
positional constraints would also require the layout's membership and visible atoms.

Positive translations preserve the source semantics in both directions. For
`never`, core emits concrete alternatives. Each implies the source negation, but a
box realization can satisfy the logical negation without satisfying any alternative.

`greedy` takes disjunctions in a supplied order and tests feasibility by existence of
a well-formed box realization. Core computes the order using its graph state.
The results here describe the relations kept for a given order.
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

/-- A primitive positional rule, with both endpoints explicit. -/
inductive Rel where
  | left (a b : Atom)
  | above (a b : Atom)
  | aligned_v (a b : Atom)
  | aligned_h (a b : Atom)
deriving DecidableEq

def holds (R : Realization) : Rel → Prop
  | .left a b  => lift₂ R {(a, b)} leftOf
  | .above a b => lift₂ R {(a, b)} above
  | .aligned_v a b => lift₂ R {(a, b)} aligned_v
  | .aligned_h a b => lift₂ R {(a, b)} aligned_h

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
-- 3. Translation to diagram-element constraints
--------------------------------------------------------------------------------

/-- A disjunction of conjunctions of diagram-element relations. -/
abbrev Disjunction := List (Finset Rel)

/-- A disjunction holds if all relations in one alternative hold. -/
def modelsDisjunction (R : Realization) (u : Disjunction) : Prop :=
  ∃ alt ∈ u, ∀ r ∈ alt, holds R r

/-- Each relation is required independently. -/
def conjuncts (l : List Rel) : List Disjunction := l.map (fun r => [{r}])

/-- The alternatives that `spytial-core` uses for `never` on one diagram-element relation. -/
def negateRelation : Rel → List Rel
  | .left a b  => [.left b a, .aligned_v a b]
  | .above a b => [.above b a, .aligned_h a b]
  | .aligned_v a b => [.left a b, .left b a]
  | .aligned_h a b => [.above a b, .above b a]

/-- Falsifying a conjunction needs one witness against one of its relations. -/
def negateConjunction (rs : List Rel) : Disjunction := (rs.flatMap negateRelation).map fun r => {r}

def orientationRels (a b : Atom) : Direction → List Rel
  | .left          => [.left b a]
  | .right         => [.left a b]
  | .above         => [.above b a]
  | .below         => [.above a b]
  | .directlyLeft  => [.left b a, .aligned_h a b]
  | .directlyRight => [.left a b, .aligned_h a b]
  | .directlyAbove => [.above b a, .aligned_v a b]
  | .directlyBelow => [.above a b, .aligned_v a b]

def alignRels (a b : Atom) : AlignDir → List Rel
  | .horizontal => [.aligned_h a b]
  | .vertical   => [.aligned_v a b]

noncomputable def pairConstraints (X : Selector₂) (facts : Atom → Atom → List Rel)
    (mode : HoldsMode) : List Disjunction :=
  X.toList.flatMap fun (a, b) =>
    match mode with
    | .always => conjuncts (facts a b)
    | .never  => [negateConjunction (facts a b)]

/-- Each axis of the circle induces an order or an alignment between two atoms. -/
private noncomputable def cyclicPair (L : List Atom) (k : Nat) (i j : Fin L.length) : List Rel :=
  let θ (p : Fin L.length) := (p.val + k) * angleStep L.length
  let x (p : Fin L.length) := Real.cos (θ p)
  let y (p : Fin L.length) := Real.sin (θ p)
  let a := L[i]
  let b := L[j]
  [if x i = x j then .aligned_v a b else if x i < x j then .left a b else .left b a,
   if y i = y j then .aligned_h a b else if y i > y j then .above a b else .above b a]

/-- All pair relations required by one rotation. Each unordered index pair is visited once. -/
noncomputable def cyclicRelations (L : List Atom) (k : Nat) : List Rel :=
  (List.finRange L.length).flatMap fun i =>
    ((List.finRange L.length).filter (i < ·)).flatMap (cyclicPair L k i)

noncomputable def cyclicDisjunction (L : List Atom) : Disjunction :=
  (List.range L.length).map fun k => (cyclicRelations L k).toFinset

noncomputable def neverCyclicDisjunctions (L : List Atom) : List Disjunction :=
  (List.range L.length).map fun k => negateConjunction (cyclicRelations L k)

noncomputable def cyclicPaths (X : Selector₂) : Rotation → List (List Atom)
  | .clockwise        => (maximalSimplePaths X).filter (fun L => 2 < L.length)
  | .counterclockwise => ((maximalSimplePaths X).map List.reverse).filter (fun L => 2 < L.length)

/-- Translate a positional constraint to disjunctions of diagram-element relations.
    An empty selector emits `some []`. An unsupported constraint returns `none`. -/
noncomputable def translate? : QualifiedConstraint → Option (List Disjunction)
  | ⟨.orientation X d, m⟩ => some (pairConstraints X (fun a b => orientationRels a b d) m)
  | ⟨.align X d, m⟩       => some (pairConstraints X (fun a b => alignRels a b d) m)
  | ⟨.cyclic X r, .always⟩ => some ((cyclicPaths X r).map cyclicDisjunction)
  | ⟨.cyclic X r, .never⟩  => some ((cyclicPaths X r).flatMap neverCyclicDisjunctions)
  | _ => none

/-! ### Satisfaction of the emitted constraints -/

lemma conjuncts_iff (R : Realization) (rs : List Rel) :
    (∀ u ∈ conjuncts rs, modelsDisjunction R u) ↔ ∀ r ∈ rs, holds R r := by
  simp [conjuncts, modelsDisjunction]

private lemma lift_pair (R : Realization) (a b : Atom) (P : Box → Box → Prop) :
    lift₂ R {(a, b)} P ↔ ∃ x y, R a = some x ∧ R b = some y ∧ P x y := by
  constructor
  · exact fun h => h (Finset.mem_singleton_self _)
  · intro h i j hij
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Finset.mem_singleton.mp hij)
    exact h

private lemma orientationRels_iff (R : Realization) (a b : Atom) (d : Direction) :
    (∀ r ∈ orientationRels a b d, holds R r) ↔ sat_orientation R {(a, b)} d := by
  cases ha : R a <;> cases hb : R b <;> cases d <;>
    simp [orientationRels, holds, sat_orientation, lift_pair, ha, hb]

private lemma alignRels_iff (R : Realization) (a b : Atom) (d : AlignDir) :
    (∀ r ∈ alignRels a b d, holds R r) ↔ sat_align R {(a, b)} d := by
  cases d <;> simp [alignRels, holds, sat_align]

private lemma negateRelation_excludes (R : Realization) {r s : Rel} (hs : s ∈ negateRelation r) :
    holds R s → ¬ holds R r := by
  cases r with
  | left a b | above a b | aligned_v a b | aligned_h a b =>
    simp only [negateRelation, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> rcases ha : R a with _ | x <;> rcases hb : R b with _ | y <;>
      simp [holds, lift_pair, ha, hb, leftOf, above, aligned_h, aligned_v]
    all_goals intros; linarith [x.width_pos, y.width_pos, x.height_pos, y.height_pos]

private lemma negateConjunction_sound {R : Realization} {rs : List Rel}
    (h : modelsDisjunction R (negateConjunction rs)) : ¬ (∀ r ∈ rs, holds R r) := by
  obtain ⟨alt, halt, hsat⟩ := h
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp halt
  obtain ⟨r, hr, hop⟩ := List.mem_flatMap.mp hs
  exact fun hall => negateRelation_excludes R hop (hsat s (Finset.mem_singleton_self s)) (hall r hr)

private lemma pairConstraints_always (R : Realization) (X : Selector₂)
    (f : Atom → Atom → List Rel) :
    (∀ u ∈ pairConstraints X f .always, modelsDisjunction R u) ↔
    ∀ p ∈ X, ∀ r ∈ f p.1 p.2, holds R r := by
  simp only [pairConstraints, List.forall_mem_flatMap, Finset.mem_toList, conjuncts_iff]

private lemma pairConstraints_never {R : Realization} {X : Selector₂} {f : Atom → Atom → List Rel}
    (h : ∀ u ∈ pairConstraints X f .never, modelsDisjunction R u) :
    ∀ p ∈ X, ¬ (∀ r ∈ f p.1 p.2, holds R r) := by
  simp only [pairConstraints, List.forall_mem_flatMap, Finset.mem_toList,
    List.forall_mem_singleton] at h
  exact fun p hp => negateConjunction_sound (h p hp)

private lemma cyclicPair_iff (R : Realization) (L : List Atom) (k : Nat) (i j : Fin L.length) :
    (∀ r ∈ cyclicPair L k i j, holds R r) ↔
    hrel R L i j k i.isLt j.isLt ∧ vrel R L i j k i.isLt j.isLt := by
  rw [cyclicPair, List.forall_mem_cons, List.forall_mem_singleton]
  apply and_congr <;> first | unfold hrel | unfold vrel
  all_goals
    dsimp only
    split_ifs <;> simp only [holds, lift_pair, nth!] <;> first
    | rfl
    | exact ⟨fun ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, h⟩,
             fun ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, h⟩⟩

private lemma cyclicRelations_iff (R : Realization) (L : List Atom) (k : Nat)
    (hlen : 2 ≤ L.length) :
    (∀ r ∈ cyclicRelations L k, holds R r) ↔ allPairs_ok R L k := by
  simp only [cyclicRelations, List.forall_mem_flatMap, List.forall_mem_filter, List.mem_finRange,
    decide_eq_true_eq, true_implies, cyclicPair_iff]
  constructor
  · intro h
    exact ⟨hlen, fun i j hij hj => h ⟨i, hij.trans hj⟩ ⟨j, hj⟩ hij⟩
  · intro h i j hij
    exact h.2 i j hij j.isLt

private lemma cyclicDisjunction_iff (R : Realization) (L : List Atom) (hlen : 2 ≤ L.length) :
    modelsDisjunction R (cyclicDisjunction L) ↔ ∃ k, k < L.length ∧ allPairs_ok R L k := by
  simp [modelsDisjunction, cyclicDisjunction, cyclicRelations_iff R L _ hlen]

private lemma neverCyclicDisjunctions_sound {R : Realization} {L : List Atom} (hlen : 2 ≤ L.length)
    (h : ∀ u ∈ neverCyclicDisjunctions L, modelsDisjunction R u) {k : Nat} (hk : k < L.length) :
    ¬ allPairs_ok R L k := by
  exact fun hall => negateConjunction_sound (h _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    ((cyclicRelations_iff R L k hlen).mpr hall)

private lemma cyclic_always_iff (R : Realization) (X : Selector₂) (rot : Rotation) :
    (∀ u ∈ (cyclicPaths X rot).map cyclicDisjunction, modelsDisjunction R u) ↔
    sat_cyclic R X rot := by
  cases rot <;>
    simp only [cyclicPaths, sat_cyclic, sat_cyclic_cw, sat_cyclic_ccw, List.forall_mem_filter,
      List.forall_mem_map, decide_eq_true_eq] <;>
    exact forall₂_congr fun L _ => imp_congr_right fun hlen => cyclicDisjunction_iff R _ hlen.le

private lemma cyclic_never_sound {R : Realization} {X : Selector₂} {rot : Rotation}
    (h : ∀ u ∈ (cyclicPaths X rot).flatMap neverCyclicDisjunctions, modelsDisjunction R u) :
    sat_never_cyclic R X rot := by
  cases rot <;>
    simp only [cyclicPaths, List.forall_mem_flatMap, List.forall_mem_filter, List.forall_mem_map,
      decide_eq_true_eq] at h <;>
    intro L hL hlen k hk <;> exact neverCyclicDisjunctions_sound hlen.le (h L hL hlen) hk

/-- An always-rule on a supported source holds exactly when all its emitted constraints hold. -/
theorem translate_always_iff {R : Realization} {c : Constraint} {us : List Disjunction}
    (hc : translate? ⟨c, .always⟩ = some us) :
    (∀ u ∈ us, modelsDisjunction R u) ↔ modelsC R c := by
  cases c <;> simp only [translate?, Option.some.injEq, reduceCtorEq] at hc <;> subst us
  case orientation X d =>
    rw [pairConstraints_always, modelsC, sat_orientation_iff_singletons]
    exact forall₂_congr fun p _ => orientationRels_iff R p.1 p.2 d
  case align X d =>
    rw [pairConstraints_always, modelsC, sat_align_iff_singletons]
    exact forall₂_congr fun p _ => alignRels_iff R p.1 p.2 d
  case cyclic X rot => exact cyclic_always_iff R X rot

/-- Each concrete witness chosen by a never-rule falsifies the corresponding positive rule. -/
theorem translate_never_sound {R : Realization} {c : Constraint} {us : List Disjunction}
    (hc : translate? ⟨c, .never⟩ = some us) (h : ∀ u ∈ us, modelsDisjunction R u) :
    modelsNegC R c := by
  cases c <;> simp only [translate?, Option.some.injEq, reduceCtorEq] at hc <;> subst us
  case orientation X d =>
    exact fun p hp hs => pairConstraints_never h p hp ((orientationRels_iff R p.1 p.2 d).mpr hs)
  case align X d =>
    exact fun p hp hs => pairConstraints_never h p hp ((alignRels_iff R p.1 p.2 d).mpr hs)
  case cyclic X rot => exact cyclic_never_sound h

theorem translate_sound {R : Realization} {q : QualifiedConstraint} {us : List Disjunction}
    (hq : translate? q = some us) (h : ∀ u ∈ us, modelsDisjunction R u) : modelsQC R q := by
  rcases q with ⟨c, _ | _⟩
  · exact (translate_always_iff hq).mp h
  · exact translate_never_sound hq h

/-- Translate a sequence of source constraints in the supplied order. -/
noncomputable def translateProgram? : List QualifiedConstraint → Option (List Disjunction)
  | [] => some []
  | q :: qs => do return (← translate? q) ++ (← translateProgram? qs)

private lemma forall_translated {qs : List QualifiedConstraint} {ds : List Disjunction}
    (h : translateProgram? qs = some ds) (P : Disjunction → Prop) :
    (∀ d ∈ ds, P d) ↔ ∀ q ∈ qs, ∃ cs, translate? q = some cs ∧ ∀ d ∈ cs, P d := by
  induction qs generalizing ds with
  | nil =>
    simp only [translateProgram?, Option.some.injEq] at h
    subst ds
    simp
  | cons q qs ih =>
    cases hq : translate? q <;> cases hqs : translateProgram? qs <;>
      simp [translateProgram?, hq, hqs] at h
    subst ds
    rw [List.forall_mem_append, List.forall_mem_cons, ih hqs]
    simp [hq]

/-- A realization satisfying the emitted constraints satisfies the source program. -/
theorem translateProgram_sound {qs : List QualifiedConstraint} {ds : List Disjunction}
    (ht : translateProgram? qs = some ds) {R : Realization} (h : ∀ d ∈ ds, modelsDisjunction R d) :
    modelsP R qs.toFinset := by
  intro q hq
  obtain ⟨cs, hc, hcs⟩ := (forall_translated ht _).mp h q (List.mem_toFinset.mp hq)
  exact translate_sound hc hcs

/-- For positive positional constraints, translation preserves the program denotation. -/
theorem denotes_eq_translated {qs : List QualifiedConstraint} {ds : List Disjunction}
    (ht : translateProgram? qs = some ds) (hpos : ∀ q ∈ qs, q.holds = .always) :
    denotes qs.toFinset = {R | R ∈ WF ∧ ∀ d ∈ ds, modelsDisjunction R d} := by
  ext R
  refine and_congr_right fun _ => ⟨fun hp => ?_, translateProgram_sound ht⟩
  refine (forall_translated ht (modelsDisjunction R)).mpr ?_
  intro q hq
  obtain ⟨cs, hc, _⟩ := (forall_translated ht (fun _ => True)).mp (by simp) q hq
  obtain ⟨c, m⟩ := q
  have hm := hpos ⟨c, m⟩ hq
  change m = .always at hm
  subst m
  exact ⟨cs, hc, (translate_always_iff hc).mpr (hp _ (List.mem_toFinset.mpr hq))⟩

--------------------------------------------------------------------------------
-- 4. The greedy construction with committed alternatives
--------------------------------------------------------------------------------

open Classical in
/-- The first alternative of `u` that is feasible together with `acc`. -/
noncomputable def pick (acc : Finset Rel) (u : Disjunction) : Option (Finset Rel) :=
  u.find? (fun alt => decide (RFeasible (acc ∪ alt)))

/-- Keep the selected alternative, or drop the disjunction if all alternatives conflict. -/
noncomputable def step (acc : Finset Rel) (u : Disjunction) : Finset Rel :=
  match pick acc u with
  | some alt => acc ∪ alt
  | none => acc

noncomputable def greedyFrom (acc : Finset Rel) (L : List Disjunction) : Finset Rel :=
  L.foldl step acc

/-- Visit the disjunctions in sequence, keeping the first feasible branch of each. -/
noncomputable def greedy (L : List Disjunction) : Finset Rel := greedyFrom ∅ L

/-- `K` keeps a branch of the disjunction `u`: all relations of one alternative are in `K`. -/
def Kept (K : Finset Rel) (u : Disjunction) : Prop := ∃ alt ∈ u, alt ⊆ K

lemma step_cases (acc : Finset Rel) (u : Disjunction) :
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

lemma subset_step (acc : Finset Rel) (u : Disjunction) : acc ⊆ step acc u := by
  rcases step_cases acc u with ⟨alt, _, _, h⟩ | ⟨_, h⟩ <;> rw [h]
  exact Finset.subset_union_left

lemma step_feasible {acc : Finset Rel} (u : Disjunction) (h : RFeasible acc) :
    RFeasible (step acc u) := by
  rcases step_cases acc u with ⟨alt, _, hF, hs⟩ | ⟨_, hs⟩ <;> rw [hs]
  · exact hF
  · exact h

lemma greedyFrom_cons (acc : Finset Rel) (u : Disjunction) (us : List Disjunction) :
    greedyFrom acc (u :: us) = greedyFrom (step acc u) us := rfl

lemma subset_greedyFrom (acc : Finset Rel) (L : List Disjunction) :
    acc ⊆ greedyFrom acc L := by
  induction L generalizing acc with
  | nil => exact subset_refl acc
  | cons u us ih =>
    rw [greedyFrom_cons]
    exact (subset_step acc u).trans (ih _)

lemma greedyFrom_feasible {acc : Finset Rel} (L : List Disjunction)
    (h : RFeasible acc) : RFeasible (greedyFrom acc L) := by
  induction L generalizing acc with
  | nil => exact h
  | cons u us ih =>
    rw [greedyFrom_cons]
    exact ih (step_feasible u h)

lemma greedyFrom_head (acc : Finset Rel) (u : Disjunction) (us : List Disjunction) :
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

lemma greedyFrom_dichotomy (acc : Finset Rel) (L : List Disjunction) :
    ∀ u ∈ L, Kept (greedyFrom acc L) u ∨
      ∀ alt ∈ u, ¬ RFeasible (greedyFrom acc L ∪ alt) := by
  induction L generalizing acc with
  | nil => intro u hu; cases hu
  | cons v vs ih =>
    intro u hu
    rcases List.mem_cons.mp hu with huv | hu'
    · rw [huv]; exact greedyFrom_head acc v vs
    · rw [greedyFrom_cons]; exact ih _ u hu'

lemma mem_greedyFrom (acc : Finset Rel) (L : List Disjunction) :
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

/-- The kept relations have a well-formed realization. -/
theorem greedy_feasible (L : List Disjunction) (hWF : WF.Nonempty) :
    RFeasible (greedy L) :=
  greedyFrom_feasible L (rfeasible_empty hWF)

/-- **Each disjunction has a kept branch, or every branch is infeasible.** If a
    disjunction is dropped, each of its alternatives conflicts with the kept
    relations. -/
theorem greedy_dichotomy (L : List Disjunction) {u : Disjunction} (hu : u ∈ L) :
    Kept (greedy L) u ∨ ∀ alt ∈ u, ¬ RFeasible (greedy L ∪ alt) :=
  greedyFrom_dichotomy ∅ L u hu

/-- A kept disjunction holds in each realization of the kept relations. -/
theorem kept_disjunction_satisfied {K : Finset Rel} {u : Disjunction} (hu : Kept K u)
    {R : Realization} (hR : R ∈ relDenotes K) : modelsDisjunction R u :=
  let ⟨alt, halt, hsub⟩ := hu
  ⟨alt, halt, fun r hr => hR.2 r (hsub hr)⟩

/-- **A constraint with all its disjunctions kept is satisfied.** -/
theorem kept_constraint_satisfied {K : Finset Rel} {q : QualifiedConstraint} {us : List Disjunction}
    (hsrc : translate? q = some us) (hq : ∀ u ∈ us, Kept K u) {R : Realization}
    (hR : R ∈ relDenotes K) : modelsQC R q :=
  translate_sound hsrc (fun u hu => kept_disjunction_satisfied (hq u hu) hR)

/-- **A violated constraint has a dropped disjunction.** -/
theorem violated_has_dropped_disjunction {K : Finset Rel} {q : QualifiedConstraint}
    {us : List Disjunction} (hsrc : translate? q = some us) {R : Realization}
    (hR : R ∈ relDenotes K) (hViol : ¬ modelsQC R q) : ∃ u ∈ us, ¬ Kept K u := by
  by_contra hNo
  push_neg at hNo
  exact hViol (kept_constraint_satisfied hsrc hNo hR)

/-- For a conjunction of individual relations, the kept set is a maximal feasible subset
    of those relations, for any supplied order. -/
theorem greedy_conjuncts_isMFS (l : List Rel) (hWF : WF.Nonempty) :
    IsMFS RFeasible l.toFinset (greedy (conjuncts l)) := by
  refine ⟨?_, greedy_feasible _ hWF, ?_⟩
  · intro r hr
    rcases mem_greedyFrom ∅ (conjuncts l) r hr with h | ⟨u, hu, alt, halt, hr'⟩
    · exact absurd h (Finset.notMem_empty r)
    · obtain ⟨r', hr'l, rfl⟩ := List.mem_map.mp hu
      rw [List.mem_singleton] at halt
      rw [halt, Finset.mem_singleton] at hr'
      rw [hr']
      exact List.mem_toFinset.mpr hr'l
  · intro c hc hcK hF
    have hu : [{c}] ∈ conjuncts l :=
      List.mem_map.mpr ⟨c, List.mem_toFinset.mp hc, rfl⟩
    rcases greedy_dichotomy (conjuncts l) hu with ⟨alt, halt, hsub⟩ | hBlocked
    · rw [List.mem_singleton] at halt
      rw [halt] at hsub
      exact hcK (hsub (Finset.mem_singleton_self c))
    · refine hBlocked {c} (List.mem_singleton.mpr rfl) (rfeasible_mono ?_ hF)
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
        at hx ⊢
      tauto

--------------------------------------------------------------------------------
-- 5. Examples
--------------------------------------------------------------------------------

/-- For `never` horizontal alignment, one box must be above the other. -/
theorem never_horizontal_branches (a b : Atom) :
    translate? ⟨.align {(a, b)} .horizontal, .never⟩ = some [[{.above a b}, {.above b a}]] := by
  simp [translate?, pairConstraints, Finset.toList_singleton, alignRels,
    negateConjunction, negateRelation]

/-- The relation "`a` is left of `b`". -/
abbrev leftOfRel := Rel.left

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

open Classical in
private lemma step_one (acc alt : Finset Rel) :
    step acc [alt] = if RFeasible (acc ∪ alt) then acc ∪ alt else acc := by
  by_cases hf : RFeasible (acc ∪ alt) <;> simp [step, pick, List.find?, hf]

/-- On (a, b), `left` followed by `directlyRight` keeps b left of a and the
    horizontal alignment from `directlyRight`. Only the conflicting order is dropped. -/
theorem directlyRight_partial_keep (a b : Atom) (hab : a ≠ b) :
    ∃ ds, translateProgram? [⟨.orientation {(a, b)} .left, .always⟩,
                             ⟨.orientation {(a, b)} .directlyRight, .always⟩] = some ds ∧
      greedy ds = {.left b a, .aligned_h a b} := by
  refine ⟨conjuncts [.left b a, .left a b, .aligned_h a b], ?_, ?_⟩
  · simp [translateProgram?, translate?, pairConstraints, Finset.toList_singleton,
      orientationRels, conjuncts]
  · have hLeft := leftOfRel_feasible b a hab.symm
    have hConflict := leftOfRel_both_infeasible a b
    have hBoth : RFeasible {Rel.aligned_h a b, .left b a} := by
      refine ⟨twoBoxes b a, twoBoxes_wf b a, fun r hr => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;>
        norm_num [holds, lift_pair, twoBoxes, hab, hab.symm, leftOf, aligned_h]
    change step (step (step ∅ [{Rel.left b a}]) [{.left a b}]) [{.aligned_h a b}] = _
    simp [step_one, leftOfRel] at hLeft hConflict ⊢
    simp [hLeft, hConflict, hBoth]
    exact Finset.pair_comm _ _

/-- **A part is kept, a part is dropped.** Let the program be the one
    constraint "`a` is left of `b` and `b` is left of `a`", with `a ≠ b`.
    It generates the two relations `leftOfRel a b` and `leftOfRel b a`.

    * At the constraint level, the only MFS is empty: the
      diagram shows nothing of the constraint.
    * At the diagram element level, each MFS keeps one relation and
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

/-- **The commitment is not maximal.** The first disjunction has two
    alternatives: "`a` is left of `b`" or "`b` is left of `a`". The
    second disjunction has one: "`b` is left of `a`". The greedy pass commits to
    the first alternative of the first disjunction, and then it must drop the
    second disjunction. But the two disjunctions can hold together. -/
theorem commit_not_maximal (a b : Atom) (hab : a ≠ b) :
    greedy [[{leftOfRel a b}, {leftOfRel b a}], [{leftOfRel b a}]]
      = {leftOfRel a b} ∧
    ∃ R ∈ WF, modelsDisjunction R [{leftOfRel a b}, {leftOfRel b a}] ∧
              modelsDisjunction R [{leftOfRel b a}] := by
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
