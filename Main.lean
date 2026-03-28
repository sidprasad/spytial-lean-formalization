/-
# Spytial: Spatial Semantics
* A program is a finite set of qualified spytial constraints.
* Each constraint carries a `HoldsMode` — currently `always` or `never` —
  mirroring the YAML `hold:` field and leaving room for future modalities.
* The denotation of a program is the set of well-formed realizations
  that satisfy those qualified constraints.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

import Std.Data.HashMap
namespace Spytial

--------------------------------------------------------------------------------
-- Atoms, Boxes, Realizations
--------------------------------------------------------------------------------

structure Atom where id : Nat
deriving BEq, DecidableEq, Hashable

structure Box where
  x_tl : ℚ
  y_tl : ℚ
  width : ℚ
  height : ℚ
deriving Repr, DecidableEq

structure GroupBoundary where
  x_tl : ℚ
  y_tl : ℚ
  x_br : ℚ
  y_br : ℚ
deriving Repr, DecidableEq

abbrev Realization := Atom → Option Box

/- primitive box relations -/

def aligned_h (b₁ b₂ : Box) : Prop := b₁.y_tl = b₂.y_tl
def aligned_v (b₁ b₂ : Box) : Prop := b₁.x_tl = b₂.x_tl
def leftOf    (b₁ b₂ : Box) : Prop := b₁.x_tl + b₁.width  < b₂.x_tl
def above     (b₁ b₂ : Box) : Prop := b₁.y_tl + b₁.height < b₂.y_tl
def contains (g : GroupBoundary) (b : Box) : Prop :=
  g.x_tl ≤ b.x_tl ∧ g.y_tl ≤ b.y_tl ∧
  b.x_tl + b.width ≤ g.x_br ∧ b.y_tl + b.height ≤ g.y_br


/- well-formed realizations  -/
def overlap (a b : Box) : Prop :=
  let h := a.x_tl < b.x_tl + b.width ∧ b.x_tl < a.x_tl + a.width
  let v := a.y_tl < b.y_tl + b.height ∧ b.y_tl < a.y_tl + a.height
  h ∧ v


/--
A realization is well-formed if:
* each box has positive dimensions,
* distinct atoms do not overlap,
* and distinct atoms map to distinct boxes.
-/
def well_formed (R : Realization) : Prop :=
  (∀ a b, R a = some b → 0 < b.width ∧ 0 < b.height) ∧
  (∀ a₁ a₂ b₁ b₂, a₁ ≠ a₂ → R a₁ = some b₁ → R a₂ = some b₂ → ¬ overlap b₁ b₂) ∧
  (∀ a₁ a₂ b, a₁ ≠ a₂ → R a₁ = some b → R a₂ ≠ some b)


/--
The universe of realizations we care about: those that are well-formed.
-/
def WF : Set Realization := { R | well_formed R }


/-- Angle step between `n` atoms on a circle. -/
noncomputable def angleStep (n : Nat) : ℝ := (2 * Real.pi) / n

--------------------------------------------------------------------------------
-- Selectors
--------------------------------------------------------------------------------
abbrev Selector₁ := Finset Atom
abbrev Selector₂ := Finset (Atom × Atom)

def first(p : Atom × Atom) : Atom := p.1
def firstOf(s : Selector₂) : Selector₁ := s.image first

def lift₁ (R : Realization) (S : Selector₁) (P : Box → Prop) : Prop :=
  ∀ {a}, a ∈ S → ∃ b, R a = some b ∧ P b

/- It turns a binary relation on boxes into a binary relation on atoms. -/
def lift₂ (R : Realization) (X : Selector₂) (P : Box → Box → Prop) : Prop :=
  ∀ {a b}, (a,b) ∈ X → ∃ ba bb, R a = some ba ∧ R b = some bb ∧ P ba bb

--------------------------------------------------------------------------------
-- Constraints
--------------------------------------------------------------------------------

inductive Direction
| above | below | left | right
| directlyAbove | directlyBelow | directlyLeft | directlyRight
deriving Repr, DecidableEq

inductive AlignDir | horizontal | vertical
deriving Repr, DecidableEq

inductive Rotation | clockwise | counterclockwise
deriving Repr, DecidableEq



inductive Constraint where
| orientation : Selector₂ → Direction → Constraint
| align       : Selector₂ → AlignDir  → Constraint
| cyclic      : Selector₂ → Rotation  → Constraint
| group₁      : Selector₁ → Constraint
| group₂      : Selector₂ → (addEdge : Bool) → Constraint
| size        : (w h : ℚ) → Selector₁ → Constraint
| hideatom    : Selector₁ → Constraint
deriving DecidableEq

/--
Modal qualifier for constraints, mirroring the YAML `hold:` field.
Currently supports `always` (default) and `never` (negation).
Designed to be extensible for future modalities.
-/
inductive HoldsMode where
  | always
  | never
  -- future: | sometimes | eventually | ...
deriving DecidableEq, Repr

/--
A constraint paired with its modal qualifier. This replaces the former
`SignedConstraint` type, aligning with spytial-core where each
`ConstraintOperation` carries a `negated : boolean` field, and
with the YAML syntax `hold: never`.
-/
structure QualifiedConstraint where
  constraint : Constraint
  holds : HoldsMode := .always
deriving DecidableEq

--------------------------------------------------------------------------------
-- Constraint Satisfaction Rules
--------------------------------------------------------------------------------


def sat_size (R : Realization) (w h : ℚ) (S : Selector₁) : Prop :=
  lift₁ R S (fun b => b.width = w ∧ b.height = h)

def sat_hide (R : Realization) (S : Selector₁) : Prop :=
  ∀ a ∈ S, R a = none

def sat_orientation (R : Realization) : Selector₂ → Direction → Prop
| X, .left            => lift₂ R X (fun b₁ b₂ => leftOf b₂ b₁)
| X, .right           => lift₂ R X leftOf
| X, .above           => lift₂ R X (fun b₁ b₂ => above b₂ b₁)
| X, .below           => lift₂ R X above
| X, .directlyLeft    => lift₂ R X (fun b₁ b₂ => leftOf b₂ b₁ ∧ aligned_h b₁ b₂)
| X, .directlyRight   => lift₂ R X (fun b₁ b₂ => leftOf b₁ b₂ ∧ aligned_h b₁ b₂)
| X, .directlyAbove   => lift₂ R X (fun b₁ b₂ => above b₂ b₁ ∧ aligned_v b₁ b₂)
| X, .directlyBelow   => lift₂ R X (fun b₁ b₂ => above b₁ b₂ ∧ aligned_v b₁ b₂)

def sat_align (R : Realization) : Selector₂ → AlignDir → Prop
| X, .horizontal => lift₂ R X aligned_h
| X, .vertical   => lift₂ R X aligned_v

--------------------------
-- Groups
--------------------------

/-- Unary grouping core (GRP1): the tightest boundary containing exactly
    the selected atoms' boxes.

   Minimality bit commented out:
    Each edge of `g` is flush with some box,
    ensuring `g` is the smallest such rectangle. -/
def sat_group₁_core (R : Realization) (S : Selector₁) : Prop :=
  ∃ g : GroupBoundary,
    (∀ a, ((∃ b, R a = some b ∧ contains g b) ↔ a ∈ S))
    -- ∧
    -- (S.Nonempty →
    --   (∃ a ∈ S, ∃ b, R a = some b ∧ g.x_tl = b.x_tl) ∧
    --   (∃ a ∈ S, ∃ b, R a = some b ∧ g.y_tl = b.y_tl) ∧
    --   (∃ a ∈ S, ∃ b, R a = some b ∧ g.x_br = b.x_tl + b.width) ∧
    --   (∃ a ∈ S, ∃ b, R a = some b ∧ g.y_br = b.y_tl + b.height))



/-- Binary grouping core (GRP2): one boundary per key `a` contains exactly the boxes of pairs `(a,b) ∈ X`. -/
def sat_group₂_core (R : Realization) (X : Selector₂) : Prop :=
  ∃ fam : Atom → GroupBoundary,
    ∀ a ∈ firstOf X,
      ∀ b, ((∃ bb, R b = some bb ∧ contains (fam a) bb) ↔ (a,b) ∈ X)

---- Cyclic -------


/-- Successor list from a binary selector (adjacency). -/
noncomputable def nextMap (X : Selector₂) : Atom → List Atom :=
  let m : Std.HashMap Atom (List Atom) :=
    X.toList.foldl (fun acc (a,b) => acc.insert a (b :: acc.getD a [])) {}
  fun a => m.getD a []

/-- All simple directed paths from `start`, length-bounded by the number of
    distinct nodes in `univ`.

    We include a `fuel : Nat` argument as a structural recursion measure.
    Lean requires that each recursive call is made on a syntactically smaller
    argument. The true termination argument is that simple paths cannot
    repeat nodes, so their length is bounded by `|univ|`. Using `fuel` with
    `fuel - 1` in each call provides Lean with the decreasing measure needed
    to accept the recursion. -/
def simplePathsFrom (start : Atom) (succ : Atom → List Atom) (univ : Finset Atom) :
  List (List Atom) :=
  let rec dfs (cur : Atom) (vis : List Atom) (fuel : Nat) : List (List Atom) :=
    if fuel = 0 then [vis.reverse]
    else if vis.contains cur then [vis.reverse]
    else (succ cur).flatMap (fun n => dfs n (cur :: vis) (fuel - 1))
  dfs start [] univ.card

/-- Boolean version for filtering. -/
def contigSubpathB (X Y : List Atom) : Bool :=
  X.length < Y.length &&
  (List.range (Y.length - X.length + 1)).any (fun j => X == (Y.drop j).take X.length)

/-- Enumerate simple paths and retain only the maximal ones w.r.t contiguous-subpath subsumption. -/
noncomputable def maximalSimplePaths (X : Selector₂) : List (List Atom) :=
  let succ  := nextMap X
  let nodes := ((X.toList.map Prod.fst) ++ (X.toList.map Prod.snd)).toFinset
  let all   := nodes.toList.flatMap (fun s => simplePathsFrom s succ nodes)
  let maxes := all.filter (fun p => !all.any (fun q => contigSubpathB p q))
  maxes

/-- Index i of list L, with proof that `i < L.length`. -/
def nth! (L : List α) (i : Nat) (h : i < L.length) : α := by
  exact L.get ⟨i, h⟩

/-- hrel and vrel as existence of visible boxes satisfying the induced relations at offset k. -/
def hrel (R : Realization) (L : List Atom) (i j k : Nat) (hi : i < L.length) (hj : j < L.length) : Prop :=
  ∃ bi bj,
    R (nth! L i hi) = some bi ∧ R (nth! L j hj) = some bj ∧
    let n   := L.length
    let st  := angleStep n
    let θi  := (i + k) * st
    let θj  := (j + k) * st
    if Real.cos θi = Real.cos θj then
      aligned_v bi bj
    else if Real.cos θi < Real.cos θj then
      leftOf bi bj
    else
      leftOf bj bi

def vrel (R : Realization) (L : List Atom) (i j k : Nat) (hi : i < L.length) (hj : j < L.length) : Prop :=
  ∃ bi bj,
    R (nth! L i hi) = some bi ∧ R (nth! L j hj) = some bj ∧
    let n   := L.length
    let st  := angleStep n
    let θi  := (i + k) * st
    let θj  := (j + k) * st
    if Real.sin θi = Real.sin θj then
      aligned_h bi bj
    else if Real.sin θi > Real.sin θj then
      above bi bj
    else
      above bj bi

/-- For a given list L and offset k, all pairwise induced h/v relations hold. -/
def allPairs_ok (R : Realization) (L : List Atom) (k : Nat) : Prop :=
  let n := L.length
  2 ≤ n ∧
  ∀ i j (hij : i < j) (hjn : j < n),
    hrel R L i j k (Nat.lt_trans hij hjn) hjn ∧
    vrel R L i j k (Nat.lt_trans hij hjn) hjn

/-- Clockwise cyclic satisfaction over maximal lists. -/
noncomputable def sat_cyclic_cw (R : Realization) (X : Selector₂) : Prop :=
  ∀ L ∈ maximalSimplePaths X,
    2 < L.length → ∃ k, k < L.length ∧ allPairs_ok R L k

/-- Counterclockwise: reuse clockwise on reversed lists. -/
noncomputable def sat_cyclic_ccw (R : Realization) (X : Selector₂) : Prop :=
  ∀ L ∈ maximalSimplePaths X,
    let L' := L.reverse
    2 < L'.length → ∃ k, k < L'.length ∧ allPairs_ok R L' k


/-- Unified API as in your constraint syntax. -/
noncomputable def sat_cyclic (R : Realization) (X : Selector₂) (rot : Rotation) : Prop :=
  match rot with
  | .clockwise        => sat_cyclic_cw  R X
  | .counterclockwise => sat_cyclic_ccw R X

--------------------------------------------------------------------------------
-- Satisfaction Predicates
--------------------------------------------------------------------------------

/-- Per-constraint satisfaction predicate (positive / `holds: always`). -/
def modelsC (R : Realization) : Constraint → Prop
| .orientation X d => sat_orientation      R X d
| .align       X a => sat_align       R X a
| .size  w h   S   => sat_size        R w h S
| .hideatom    S   => sat_hide        R S
| .group₁      S   => sat_group₁_core R S
| .group₂      X _ => sat_group₂_core R X
| .cyclic      X r => sat_cyclic      R X r

/-- Negated constraint satisfaction (`holds: never`).
    Negation is the precise logical ¬ of the positive predicate. -/
def modelsNegC (R : Realization) : Constraint → Prop
| c => ¬ modelsC R c

/--
Satisfaction for qualified constraints.  Dispatches to `modelsC` or
`modelsNegC` based on the `HoldsMode`.
-/
def modelsQC (R : Realization) : QualifiedConstraint → Prop
| ⟨c, .always⟩ => modelsC R c
| ⟨c, .never⟩  => modelsNegC R c

@[simp] lemma modelsQC_always (R : Realization) (c : Constraint) :
  modelsQC R ⟨c, .always⟩ ↔ modelsC R c := by
  rfl

@[simp] lemma modelsQC_never (R : Realization) (c : Constraint) :
  modelsQC R ⟨c, .never⟩ ↔ modelsNegC R c := by
  rfl


--------- Semantics ---------

/--
 From a spatial perspective, the semantics of a program (set of qualified
 constraints) is the set of well-formed realizations that satisfy all of them.

 Program composition is set union,
 and a realization satisfies a program if it satisfies each qualified constraint.
-/

abbrev Program := Finset QualifiedConstraint

def compose (P Q : Program) : Program := P ∪ Q


/-- Program satisfaction: a realization models a program iff it satisfies
    every qualified constraint in the program. -/
def modelsP (R : Realization) (P : Program) : Prop :=
  ∀ c ∈ P, modelsQC R c

--------------------------------------------------------------------------------
-- Denotational Semantics
--------------------------------------------------------------------------------


/--
The denotation of a *program* is the set of realizations
that satisfy all qualified constraints in the program,
and are well-formed.
-/
def denotes (P : Program) : Set Realization :=
  { R | R ∈ WF ∧ modelsP R P }

notation "⟦" P "⟧" => denotes P

theorem denotes_empty : ⟦∅⟧ = WF := by
  ext R; simp [denotes, modelsP]



--------------------------------------------------------------------------------
-- Key Meta Theorems
--------------------------------------------------------------------------------


/-- Adding a qualified constraint refines the denotation (shrinks the set).
    Singleton case of `antimonotonicity`. -/
lemma refinement (P : Program) (C : QualifiedConstraint) :
  denotes (P ∪ {C}) ⊆ ⟦P⟧ := by
  intro R ⟨hWF, hSat⟩
  exact ⟨hWF, fun c hc => hSat c (Finset.mem_union_left {C} hc)⟩


/--
**Antimonotonicity.** More constraints ⟹ smaller denotation.
The denotation map is contravariant: `P ⊆ Q → ⟦Q⟧ ⊆ ⟦P⟧`.
-/
theorem antimonotonicity {P Q : Program} (hPQ : P ⊆ Q) : (denotes Q) ⊆ (denotes P) := by
  intro R ⟨hWF, hSat⟩
  exact ⟨hWF, fun c hc => hSat c (hPQ hc)⟩


/--
The denotation of an unsatisfiable program is empty.
-/
lemma unsat_empty {P : Program} (hUnsat : ∀ R ∈ WF, ¬ modelsP R P) :
  denotes P = ∅ := by
  ext R
  simp only [denotes, modelsP, Set.mem_setOf, Set.mem_empty_iff_false, iff_false]
  intro ⟨hWF, hSat⟩
  exact hUnsat R hWF hSat

lemma empty_unsat {P : Program} (hEmpty : denotes P = ∅) :
  ∀ R ∈ WF, ¬ modelsP R P := by
  intro R hWF hSat
  have : R ∈ denotes P := by
    simp only [denotes, modelsP, Set.mem_setOf]
    exact ⟨hWF, hSat⟩
  rw [hEmpty] at this
  exact (Set.mem_empty_iff_false R).mp this

/-- A program is unsatisfiable iff its denotation is empty. -/
theorem unsat_iff_empty (P : Program) :
  denotes P = ∅ ↔ (∀ R ∈ WF, ¬ modelsP R P) := by
  constructor
  · exact empty_unsat
  · exact unsat_empty


--------------------------------------------------------------------------------
-- Denotation Set Difference
--------------------------------------------------------------------------------

/-- Set difference of denotations: realizations satisfying P but not Q. -/
def denoteDiff (P Q : Program) : Set Realization := denotes P \ denotes Q

lemma denoteDiff_sub (P Q : Program) : denoteDiff P Q ⊆ denotes P :=
  Set.diff_subset

lemma denoteDiff_union (P Q : Program) :
    denoteDiff P Q ∪ (denotes P ∩ denotes Q) = denotes P :=
  Set.diff_union_inter (denotes P) (denotes Q)

/-- The difference is empty iff ⟦P⟧ ⊆ ⟦Q⟧. -/
lemma denoteDiff_empty_iff (P Q : Program) :
    denoteDiff P Q = ∅ ↔ denotes P ⊆ denotes Q := by
  simp [denoteDiff, Set.diff_eq_empty]

/-- Adding constraints to P shrinks the difference. -/
lemma denoteDiff_antitone_left {P₁ P₂ : Program} (h : P₁ ⊆ P₂) (Q : Program) :
    denoteDiff P₂ Q ⊆ denoteDiff P₁ Q :=
  Set.diff_subset_diff_left (antimonotonicity h)

/-- Adding constraints to Q enlarges the difference (⟦Q⟧ shrinks,
    so less is subtracted). -/
lemma denoteDiff_antitone_right {Q₁ Q₂ : Program} (h : Q₁ ⊆ Q₂) (P : Program) :
    denoteDiff P Q₁ ⊆ denoteDiff P Q₂ :=
  Set.diff_subset_diff_right (antimonotonicity h)

/-- Composition (program union) equals the intersection of individual
    denotations. -/
theorem compose_eq_inter (P Q : Program) :
    denotes (compose P Q) = denotes P ∩ denotes Q := by
  ext R
  simp only [denotes, compose, modelsP, Set.mem_inter_iff, Set.mem_setOf]
  constructor
  · intro ⟨hWF, hSat⟩
    exact ⟨⟨hWF, fun c hc => hSat c (Finset.mem_union_left Q hc)⟩,
           ⟨hWF, fun c hc => hSat c (Finset.mem_union_right P hc)⟩⟩
  · intro ⟨⟨hWF, hSatP⟩, ⟨_, hSatQ⟩⟩
    exact ⟨hWF, fun c hc => by
      rcases Finset.mem_union.mp hc with h | h
      · exact hSatP c h
      · exact hSatQ c h⟩

--------------------------------------------------------------------------------
-- Pure Negation: Contradiction and Complement
--------------------------------------------------------------------------------

/-- Exhaustiveness: every realization satisfies one mode. -/
theorem pure_neg_exhaustive (c : Constraint)
    (R : Realization) : modelsC R c ∨ modelsNegC R c := by
  by_cases h : modelsC R c
  · exact Or.inl h
  · exact Or.inr h

/-- Exclusivity: no realization satisfies both modes. -/
theorem pure_neg_exclusive (c : Constraint)
    (R : Realization) : ¬ (modelsC R c ∧ modelsNegC R c) :=
  fun ⟨hPos, hNeg⟩ => hNeg hPos

/-- A program with both `holds: always` and `holds: never` for the
    same constraint is unsatisfiable. -/
theorem always_never_unsat (P : Program) (c : Constraint)
    (hA : ⟨c, .always⟩ ∈ P) (hN : ⟨c, .never⟩ ∈ P) :
    denotes P = ∅ := by
  apply unsat_empty
  intro R _ hSat
  exact pure_neg_exclusive c R ⟨hSat _ hA, hSat _ hN⟩

/-- Complement intersection: ⟦{c, always}⟧ ∩ ⟦{c, never}⟧ = ∅. -/
lemma pure_neg_complement_inter (c : Constraint) :
    denotes {⟨c, .always⟩} ∩ denotes {⟨c, .never⟩} = ∅ := by
  ext R
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨hA, hN⟩
  simp only [denotes, modelsP, Set.mem_setOf] at hA hN
  obtain ⟨_, hSatA⟩ := hA
  obtain ⟨_, hSatN⟩ := hN
  exact pure_neg_exclusive c R
    ⟨hSatA _ (Finset.mem_singleton.mpr rfl), hSatN _ (Finset.mem_singleton.mpr rfl)⟩

--------------------------------------------------------------------------------
-- Orientation Contradiction
--------------------------------------------------------------------------------

/-- With pure negation, a program requiring both `holds: always` and
    `holds: never` for the same orientation constraint is unsatisfiable.
    This is now a direct corollary of `always_never_unsat`. -/
lemma orientation_always_never_unsat (P : Program) (X : Selector₂) (d : Direction)
    (hA : ⟨.orientation X d, .always⟩ ∈ P)
    (hN : ⟨.orientation X d, .never⟩ ∈ P) :
    denotes P = ∅ :=
  always_never_unsat P (.orientation X d) hA hN

--------------------------------------------------------------------------------
-- Set Difference Decomposition
--------------------------------------------------------------------------------

/-- Finset-level program difference: ⟦P \ Q⟧ ⊇ ⟦P⟧.
    Removing constraints from P weakens the program. -/
lemma denotes_sdiff_supset (P Q : Program) : denotes P ⊆ denotes (P \ Q) :=
  antimonotonicity Finset.sdiff_subset

/-- The denotation set-difference is contained in the program-difference
    denotation: ⟦P⟧ \ ⟦Q⟧ ⊆ ⟦P \ Q⟧. -/
lemma denoteDiff_sub_sdiff (P Q : Program) : denoteDiff P Q ⊆ denotes (P \ Q) :=
  Set.diff_subset.trans (denotes_sdiff_supset P Q)

/-- Flip the holds mode of a qualified constraint.
    `always ↔ never` — used to express "violates q" as "satisfies flipMode q". -/
def flipMode : QualifiedConstraint → QualifiedConstraint
| ⟨c, .always⟩ => ⟨c, .never⟩
| ⟨c, .never⟩  => ⟨c, .always⟩

/-- Flipping mode negates satisfaction. -/
lemma flipMode_neg (q : QualifiedConstraint) (R : Realization) :
    modelsQC R (flipMode q) ↔ ¬ modelsQC R q := by
  rcases q with ⟨c, (_ | _)⟩
  · exact Iff.rfl
  · exact not_not.symm

/-- **Set difference decomposition.**

    ⟦P⟧ \ ⟦Q⟧ = ⋃ q ∈ Q, ⟦P ∪ {flipMode q}⟧

    Each summand adds the negation of one specific constraint from Q.
    This shows that the denotation algebra is closed under set difference
    up to finite union (which programs cannot express internally, since
    programs are conjunctive). -/
theorem denoteDiff_decompose (P Q : Program) :
    denoteDiff P Q = ⋃ q ∈ Q, denotes (P ∪ {flipMode q}) := by
  ext R
  simp only [denoteDiff, Set.mem_diff, Set.mem_iUnion₂]
  constructor
  · -- Forward: R ∈ ⟦P⟧ ∧ R ∉ ⟦Q⟧ → ∃ q ∈ Q, R ∈ ⟦P ∪ {flipMode q}⟧
    intro ⟨hRP, hRQ⟩
    have hWF : R ∈ WF := hRP.1
    have hNMQ : ¬ modelsP R Q := fun h => hRQ ⟨hWF, h⟩
    simp only [modelsP] at hNMQ; push_neg at hNMQ
    obtain ⟨q, hqQ, hNeg⟩ := hNMQ
    refine ⟨q, hqQ, hWF, fun c hc => ?_⟩
    rcases Finset.mem_union.mp hc with hP | hF
    · exact hRP.2 c hP
    · rw [Finset.mem_singleton.mp hF]
      exact (flipMode_neg q R).mpr hNeg
  · -- Reverse: ∃ q ∈ Q, R ∈ ⟦P ∪ {flipMode q}⟧ → R ∈ ⟦P⟧ ∧ R ∉ ⟦Q⟧
    intro ⟨q, hqQ, hWF, hSat⟩
    refine ⟨⟨hWF, fun c hc => hSat c (Finset.mem_union_left _ hc)⟩, ?_⟩
    intro ⟨_, hMQ⟩
    have hFlip := hSat (flipMode q) (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
    rw [flipMode_neg q R] at hFlip
    exact hFlip (hMQ q hqQ)

/-- **Under-approximation of set difference.** For any q ∈ Q,
    ⟦P ∪ {flipMode q}⟧ ⊆ ⟦P⟧ \ ⟦Q⟧.
    If R satisfies flip(q), it violates q, so `modelsP R Q` fails.
    -/
lemma denoteDiff_approx (P Q : Program) (q : QualifiedConstraint)
    (hq : q ∈ Q) :
    denotes (P ∪ {flipMode q}) ⊆ denoteDiff P Q := by
  intro R hR
  refine ⟨antimonotonicity Finset.subset_union_left hR, ?_⟩
  intro ⟨_, hSatQ⟩
  obtain ⟨_, hSatPF⟩ := hR
  have hFlip := hSatPF (flipMode q) (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
  exact ((flipMode_neg q R).mp hFlip) (hSatQ q hq)

/-- **Existence of a program under-approximating set difference.**
    For any programs P and Q with q ∈ Q, there exists a program M whose
    denotation is contained in ⟦P⟧ \ ⟦Q⟧. Direct corollary of
    `denoteDiff_approx`. -/
lemma denoteDiff_witness (P Q : Program)
    (q : QualifiedConstraint) (hq : q ∈ Q) :
    ∃ M : Program, denotes M ⊆ denoteDiff P Q :=
  ⟨P ∪ {flipMode q}, denoteDiff_approx P Q q hq⟩


--------------------------------------------------------------------------------
-- Program Equivalence & Algebraic Structure
--------------------------------------------------------------------------------

/-- Semantic program equivalence: two programs are equivalent iff they
    have the same denotation. -/
def prog_equiv (P Q : Program) : Prop := denotes P = denotes Q

infix:50 " ≃ₚ " => prog_equiv

/-- Denotation is always within the well-formed universe. -/
theorem denotes_sub_WF (P : Program) : denotes P ⊆ WF := by
  intro R hR; exact hR.1

/-- Program equivalence is reflexive. -/
lemma prog_equiv_refl (P : Program) : P ≃ₚ P := rfl

/-- Program equivalence is symmetric. -/
lemma prog_equiv_symm {P Q : Program} (h : P ≃ₚ Q) : Q ≃ₚ P := h.symm

/-- Program equivalence is transitive. -/
lemma prog_equiv_trans {P Q R : Program} (h₁ : P ≃ₚ Q) (h₂ : Q ≃ₚ R) : P ≃ₚ R :=
  h₁.trans h₂

/-- **Composition is commutative** (up to semantic equivalence). -/
theorem compose_comm (P Q : Program) : compose P Q ≃ₚ compose Q P := by
  simp [prog_equiv, compose_eq_inter, Set.inter_comm]

/-- **Composition is associative** (up to semantic equivalence). -/
theorem compose_assoc (P Q R : Program) :
    compose (compose P Q) R ≃ₚ compose P (compose Q R) := by
  simp [prog_equiv, compose_eq_inter, Set.inter_assoc]

/-- **Composition is idempotent**: composing a program with itself changes nothing. -/
theorem compose_idem (P : Program) : compose P P ≃ₚ P := by
  simp [prog_equiv, compose_eq_inter, Set.inter_self]

/-- **Empty program is a left identity** for composition. -/
theorem compose_empty_left (P : Program) : compose ∅ P ≃ₚ P := by
  unfold prog_equiv
  rw [compose_eq_inter, denotes_empty]
  exact Set.inter_eq_right.mpr (denotes_sub_WF P)

/-- **Empty program is a right identity** for composition. -/
theorem compose_empty_right (P : Program) : compose P ∅ ≃ₚ P := by
  simp only [prog_equiv, compose_eq_inter, denotes_empty]
  exact Set.inter_eq_left.mpr (denotes_sub_WF P)

/-- **Congruence**: program equivalence is preserved under composition. -/
theorem compose_congr {P₁ P₂ Q₁ Q₂ : Program}
    (hP : P₁ ≃ₚ P₂) (hQ : Q₁ ≃ₚ Q₂) :
    compose P₁ Q₁ ≃ₚ compose P₂ Q₂ := by
  unfold prog_equiv at *
  simp only [compose_eq_inter, hP, hQ]

--------------------------------------------------------------------------------
-- Semantic Entailment
--------------------------------------------------------------------------------

/-- Semantic entailment: program P entails qualified constraint q
    iff every realization in ⟦P⟧ satisfies q. -/
def entails (P : Program) (q : QualifiedConstraint) : Prop :=
  ∀ R ∈ denotes P, modelsQC R q

/-- Entailment is equivalent to denotation inclusion. -/
theorem entails_iff_subset (P : Program) (q : QualifiedConstraint) :
    entails P q ↔ denotes P ⊆ denotes {q} := by
  constructor
  · intro hE R hR
    refine ⟨hR.1, fun c hc => ?_⟩
    rw [Finset.mem_singleton.mp hc]
    exact hE R hR
  · intro hS R hR
    have := hS hR
    exact this.2 q (Finset.mem_singleton.mpr rfl)

/-- **Redundancy**: adding an already-entailed constraint is a no-op. -/
theorem constraint_redundant (P : Program) (q : QualifiedConstraint)
    (hE : entails P q) : P ≃ₚ (P ∪ {q}) := by
  ext R
  simp only [denotes, modelsP, Set.mem_setOf]
  constructor
  · intro ⟨hWF, hSat⟩
    refine ⟨hWF, fun c hc => ?_⟩
    rcases Finset.mem_union.mp hc with h | h
    · exact hSat c h
    · rw [Finset.mem_singleton.mp h]
      exact hE R ⟨hWF, hSat⟩
  · intro ⟨hWF, hSat⟩
    exact ⟨hWF, fun c hc => hSat c (Finset.mem_union_left _ hc)⟩

--------------------------------------------------------------------------------
-- Atom Footprint & Frame Rule
--------------------------------------------------------------------------------

/-- Extract the set of atoms mentioned by a constraint. -/
def atoms_of_constraint : Constraint → Finset Atom
| .orientation X _  => X.image Prod.fst ∪ X.image Prod.snd
| .align       X _  => X.image Prod.fst ∪ X.image Prod.snd
| .cyclic      X _  => X.image Prod.fst ∪ X.image Prod.snd
| .group₁      S    => S
| .group₂      X _  => X.image Prod.fst ∪ X.image Prod.snd
| .size    _ _  S   => S
| .hideatom    S    => S

/-- Atoms mentioned by a program. -/
def atoms_of_program (P : Program) : Finset Atom :=
  P.biUnion (fun qc => atoms_of_constraint qc.constraint)

--------------------------------------------------------------------------------
-- Cyclic Constraint Properties
--------------------------------------------------------------------------------

/-- CW/CCW duality: counterclockwise satisfaction is clockwise satisfaction
    on the reversed list. This is definitional but stated explicitly for
    reference. -/
lemma cyclic_ccw_eq_cw_reverse (R : Realization) (X : Selector₂) :
    sat_cyclic_ccw R X =
      (∀ L ∈ maximalSimplePaths X,
        2 < L.reverse.length → ∃ k, k < L.reverse.length ∧ allPairs_ok R L.reverse k) :=
  rfl

/-- `leftOf` is asymmetric for boxes with non-negative widths:
    if b₁ is left of b₂, then b₂ cannot be left of b₁. -/
lemma leftOf_asymm {b₁ b₂ : Box} (hw₁ : 0 ≤ b₁.width) (hw₂ : 0 ≤ b₂.width)
    (h : leftOf b₁ b₂) : ¬ leftOf b₂ b₁ := by
  intro h'
  unfold leftOf at h h'
  linarith

/-- `above` is asymmetric for boxes with non-negative heights. -/
lemma above_asymm {b₁ b₂ : Box} (hh₁ : 0 ≤ b₁.height) (hh₂ : 0 ≤ b₂.height)
    (h : above b₁ b₂) : ¬ above b₂ b₁ := by
  intro h'
  unfold above at h h'
  linarith

/-- For n ≥ 3, the angles `k · angleStep n` and `(n-1+k) · angleStep n` cannot
    have both equal cosine and equal sine. This is because their difference
    `(n-1) · (2π/n) = 2π(1 - 1/n)` is not a multiple of 2π for n ≥ 3,
    so the two points on the unit circle are distinct. -/
lemma angle_pair_not_both_eq (n : ℕ) (hn : 2 < n) (k : ℕ) :
    ¬ (Real.cos (k * angleStep n) = Real.cos ((↑(n - 1) + k) * angleStep n) ∧
       Real.sin (k * angleStep n) = Real.sin ((↑(n - 1) + k) * angleStep n)) := by
  intro ⟨hc, hs⟩
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have step_def : angleStep n = 2 * Real.pi / n := rfl
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [Real.cos_eq_cos_iff] at hc
  -- Helper: derive (n-1) = m*n (ℤ) from (n-1)*step = 2mπ, then show impossible
  have derive_impossible : ∀ (m : ℤ),
      (↑(n - 1) : ℝ) * angleStep n = 2 * ↑m * Real.pi → False := by
    intro m h1
    -- angleStep n = 2π/n, so (n-1) * (2π/n) = 2mπ
    -- ⟹ (n-1) * 2π = 2mπ * n ⟹ (n-1) = m * n
    have hst : angleStep n * ↑n = 2 * Real.pi := by
      unfold angleStep; field_simp
    -- Multiply h1 by n
    have h2 : (↑(n - 1) : ℝ) * (2 * Real.pi) = 2 * ↑m * Real.pi * ↑n := by
      calc (↑(n - 1) : ℝ) * (2 * Real.pi)
          = ↑(n - 1) * (angleStep n * ↑n) := by rw [hst]
        _ = (↑(n - 1) * angleStep n) * ↑n := by ring
        _ = (2 * ↑m * Real.pi) * ↑n := by rw [h1]
        _ = 2 * ↑m * Real.pi * ↑n := by ring
    have h3 : (↑(n - 1) : ℝ) = ↑m * ↑n := by nlinarith [Real.pi_pos]
    -- (n-1 : ℕ) = n - 1 since n ≥ 3
    have hcast : (↑(n - 1 : ℕ) : ℝ) = (↑n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
    rw [hcast] at h3
    -- h3 : (↑n : ℝ) - 1 = ↑m * ↑n → n - 1 = m * n in ℤ
    have h4 : (n : ℤ) - 1 = m * ↑n := by
      have : ((n : ℤ) : ℝ) - 1 = (m : ℝ) * (n : ℝ) := h3
      exact_mod_cast this
    -- m * n = n - 1 with n ≥ 3: impossible since 0 < n-1 < n
    -- m = 0 → n - 1 = 0 → n = 1, but n ≥ 3
    -- m ≥ 1 → m * n ≥ n > n - 1
    -- m ≤ -1 → m * n ≤ -n < 0 ≤ n - 1
    have hn_int : (3 : ℤ) ≤ ↑n := by exact_mod_cast hn
    rcases le_or_lt m 0 with hm | hm
    · rcases eq_or_lt_of_le hm with rfl | hm'
      · simp at h4; omega
      · have : m * (n : ℤ) ≤ -↑n := by nlinarith
        omega
    · have : m * (n : ℤ) ≥ ↑n := by nlinarith
      omega
  obtain ⟨m, hm | hm⟩ := hc
  · -- Case: (n-1+k)*step = 2mπ + k*step → (n-1)*step = 2mπ
    exact derive_impossible m (by linarith)
  · -- Case: (n-1+k)*step = 2mπ - k*step
    rw [Real.sin_eq_sin_iff] at hs
    obtain ⟨m', hm' | hm'⟩ := hs
    · -- sin case 1: y = 2m'π + x → (n-1)*step = 2m'π
      exact derive_impossible m' (by linarith)
    · -- sin case 2: y = (2m'+1)π - x → x + y = (2m'+1)π
      -- cos case 2: x + y = 2mπ → 2mπ = (2m'+1)π → 2m = 2m'+1 (impossible)
      have hsum1 : (↑k * angleStep n + (↑(n - 1) + ↑k) * angleStep n) =
          2 * ↑m * Real.pi := by linarith
      have hsum2 : (↑k * angleStep n + (↑(n - 1) + ↑k) * angleStep n) =
          (2 * ↑m' + 1) * Real.pi := by linarith
      have : (2 * ↑m : ℝ) * Real.pi = (2 * ↑m' + 1) * Real.pi := by linarith
      have : (2 * ↑m : ℝ) = 2 * ↑m' + 1 := by
        exact mul_right_cancel₀ (ne_of_gt Real.pi_pos) this
      have : (2 * m : ℤ) = 2 * m' + 1 := by exact_mod_cast this
      omega

/-- **Cyclic CW+CCW contradiction.** A program requiring both clockwise
    and counterclockwise cyclic layout on the same selector is unsatisfiable,
    provided the selector induces at least one maximal path of length > 2.

    **Proof sketch**: For any list L of length n ≥ 3, `allPairs_ok R L k` (CW)
    and `allPairs_ok R L.reverse k'` (CCW) impose contradictory spatial
    constraints. The pair `(0, n-1)` in L corresponds to the pair `(0, n-1)` in
    L.reverse but with atoms **swapped** (L.reverse[0] = L[n-1], L.reverse[n-1] = L[0]).
    This produces `hrel`/`vrel` constraints on the same two boxes with swapped arguments.

    The contradiction follows by case analysis on the cos/sin comparisons:
    - If CW and CCW cos comparisons go the **same way** (both < or both >):
      the swapped atom order forces `leftOf A B ∧ leftOf B A` → `leftOf_asymm`.
    - If both cos comparisons give **aligned_v**: check `vrel` (sin). If both
      sin go the same way → `above_asymm`. If both give **aligned_h**: then
      `angle_pair_not_both_eq` shows the angles can't match for n ≥ 3.
    - If cos comparisons go **opposite ways**: hrel is consistent, but then
      one must examine additional pairs (e.g., (0,1) and (1,2)) to find
      a contradictory triple. This requires a multi-pair chirality argument
      using the fact that CW and CCW assign angles in opposite circular order.

    The single-pair cases are discharged by `leftOf_asymm`, `above_asymm`,
    and `angle_pair_not_both_eq` (all proven). The multi-pair chirality
    argument is the remaining sorry. -/
theorem cyclic_cw_ccw_unsat (P : Program) (X : Selector₂)
    (hCW : ⟨.cyclic X .clockwise, .always⟩ ∈ P)
    (hCCW : ⟨.cyclic X .counterclockwise, .always⟩ ∈ P)
    (hNontriv : ∃ L ∈ maximalSimplePaths X, 2 < L.length) :
    denotes P = ∅ := by
  apply unsat_empty
  intro R hWF hSat
  obtain ⟨L, hLmem, hLlen⟩ := hNontriv
  have hCWsat := hSat ⟨.cyclic X .clockwise, .always⟩ hCW
  have hCCWsat := hSat ⟨.cyclic X .counterclockwise, .always⟩ hCCW
  simp only [modelsQC, modelsC] at hCWsat hCCWsat
  have hCW_L := hCWsat L hLmem hLlen
  have hCCW_L := hCCWsat L hLmem (by rwa [List.length_reverse])
  -- hCW_L : ∃ k, k < L.length ∧ allPairs_ok R L k
  -- hCCW_L : ∃ k, k < L.reverse.length ∧ allPairs_ok R L.reverse k
  -- Supporting lemmas proven:
  --   angle_pair_not_both_eq : distinct circle positions for n ≥ 3
  --   leftOf_asymm / above_asymm : spatial relation asymmetry
  -- Remaining: multi-pair chirality argument for opposite-direction cases
  sorry

--------------------------------------------------------------------------------
-- Opposite Orientation Contradiction
--------------------------------------------------------------------------------

/-- `leftOf` is irreflexive for boxes with positive width. -/
lemma leftOf_irrefl {b : Box} (hw : 0 < b.width) : ¬ leftOf b b := by
  intro h; unfold leftOf at h; linarith

/-- Two opposite orientation constraints on the same nonempty selector
    are contradictory. E.g., requiring atoms to be both left and right
    of each other simultaneously is unsatisfiable. -/
theorem opposite_orientation_unsat (P : Program) (X : Selector₂)
    (hA : ⟨.orientation X .left, .always⟩ ∈ P)
    (hB : ⟨.orientation X .right, .always⟩ ∈ P)
    (hNE : X.Nonempty) :
    denotes P = ∅ := by
  apply unsat_empty
  intro R hWF hSat
  -- Extract the satisfaction predicates (modelsC level)
  have hL : modelsC R (.orientation X .left) := hSat _ hA
  have hR : modelsC R (.orientation X .right) := hSat _ hB
  -- Unfold to lift₂
  simp only [modelsC, sat_orientation] at hL hR
  obtain ⟨⟨a, b⟩, hab⟩ := hNE
  obtain ⟨ba, bb, hba, hbb, hLeft⟩ := hL hab
  obtain ⟨ba', bb', hba', hbb', hRight⟩ := hR hab
  rw [hba] at hba'; cases hba'
  rw [hbb] at hbb'; cases hbb'
  have hWFR := hWF
  simp only [WF, Set.mem_setOf, well_formed] at hWFR
  obtain ⟨hPos, _, _⟩ := hWFR
  obtain ⟨hw_a, _⟩ := hPos a ba hba
  obtain ⟨hw_b, _⟩ := hPos b bb hbb
  exact leftOf_asymm (le_of_lt hw_b) (le_of_lt hw_a) hLeft hRight

/-- Above/below contradiction: requiring atoms to be both above and below
    each other simultaneously is unsatisfiable. -/
theorem opposite_vertical_unsat (P : Program) (X : Selector₂)
    (hA : ⟨.orientation X .above, .always⟩ ∈ P)
    (hB : ⟨.orientation X .below, .always⟩ ∈ P)
    (hNE : X.Nonempty) :
    denotes P = ∅ := by
  apply unsat_empty
  intro R hWF hSat
  have hAbove : modelsC R (.orientation X .above) := hSat _ hA
  have hBelow : modelsC R (.orientation X .below) := hSat _ hB
  simp only [modelsC, sat_orientation] at hAbove hBelow
  obtain ⟨⟨a, b⟩, hab⟩ := hNE
  obtain ⟨ba, bb, hba, hbb, hAb⟩ := hAbove hab
  obtain ⟨ba', bb', hba', hbb', hBe⟩ := hBelow hab
  rw [hba] at hba'; cases hba'
  rw [hbb] at hbb'; cases hbb'
  have hWFR := hWF
  simp only [WF, Set.mem_setOf, well_formed] at hWFR
  obtain ⟨hPos, _, _⟩ := hWFR
  obtain ⟨_, hh_a⟩ := hPos a ba hba
  obtain ⟨_, hh_b⟩ := hPos b bb hbb
  exact above_asymm (le_of_lt hh_b) (le_of_lt hh_a) hAb hBe

--------------------------------------------------------------------------------
-- Summary of Main Theorems
--------------------------------------------------------------------------------

-- Algebraic Structure
#check denotes_empty       -- ⟦∅⟧ = WF
#check compose_eq_inter    -- ⟦P ∪ Q⟧ = ⟦P⟧ ∩ ⟦Q⟧
#check antimonotonicity    -- P ⊆ Q → ⟦Q⟧ ⊆ ⟦P⟧
#check denotes_sub_WF      -- ⟦P⟧ ⊆ WF

-- Program Algebra (commutative idempotent monoid)
#check compose_comm        -- P ∪ Q ≃ₚ Q ∪ P
#check compose_assoc       -- (P ∪ Q) ∪ R ≃ₚ P ∪ (Q ∪ R)
#check compose_idem        -- P ∪ P ≃ₚ P
#check compose_empty_left  -- ∅ ∪ P ≃ₚ P
#check compose_congr       -- congruence

-- Unsatisfiability
#check unsat_iff_empty     -- ⟦P⟧ = ∅ ↔ unsatisfiable
#check always_never_unsat  -- always + never = ∅

-- Negation
#check pure_neg_exhaustive -- modelsC ∨ modelsNegC
#check pure_neg_exclusive  -- ¬(modelsC ∧ modelsNegC)

-- Entailment
#check entails_iff_subset  -- entails P q ↔ ⟦P⟧ ⊆ ⟦{q}⟧
#check constraint_redundant -- entailed ⟹ no-op

-- Closure / Approximation
#check denoteDiff_decompose -- ⟦P⟧ \ ⟦Q⟧ = ⋃ q ∈ Q, ⟦P ∪ {flip q}⟧

-- Constraint-Specific Contradictions
#check cyclic_cw_ccw_unsat       -- CW + CCW = ∅ (sorry: geometric core)
#check opposite_orientation_unsat -- left + right = ∅
#check opposite_vertical_unsat   -- above + below = ∅

end Spytial
