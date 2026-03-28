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

lemma denotes_empty : ⟦∅⟧ = WF := by
  ext R; simp [denotes, modelsP]



--------------------------------------------------------------------------------
-- Key Meta Theorems
--------------------------------------------------------------------------------


/--
Adding a qualified constraint refines the denotation (shrinks the set).
-/
theorem refinement (P : Program) (C : QualifiedConstraint) :
  denotes (P ∪ {C}) ⊆ ⟦P⟧ := by
  intro R ⟨hWF, hSat⟩
  exact ⟨hWF, fun c hc => hSat c (Finset.mem_union_left {C} hc)⟩


/--
Corollary to `refinement`. If a program `P` is a subset of `Q`,
then the denotation of `Q` is a superset of the denotation of `P`.
-/
theorem monotonicity {P Q : Program} (hPQ : P ⊆ Q) : (denotes Q) ⊆ (denotes P) := by
  intro R ⟨hWF, hSat⟩
  exact ⟨hWF, fun c hc => hSat c (hPQ hc)⟩


/--
The denotation of an unsatisfiable program is empty.
-/
theorem unsat_empty {P : Program} (hUnsat : ∀ R ∈ WF, ¬ modelsP R P) :
  denotes P = ∅ := by
  ext R
  simp only [denotes, modelsP, Set.mem_setOf, Set.mem_empty_iff_false, iff_false]
  intro ⟨hWF, hSat⟩
  exact hUnsat R hWF hSat

theorem empty_unsat {P : Program} (hEmpty : denotes P = ∅) :
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

theorem denoteDiff_sub (P Q : Program) : denoteDiff P Q ⊆ denotes P :=
  Set.diff_subset

theorem denoteDiff_union (P Q : Program) :
    denoteDiff P Q ∪ (denotes P ∩ denotes Q) = denotes P :=
  Set.diff_union_inter (denotes P) (denotes Q)

/-- The difference is empty iff ⟦P⟧ ⊆ ⟦Q⟧. -/
theorem denoteDiff_empty_iff (P Q : Program) :
    denoteDiff P Q = ∅ ↔ denotes P ⊆ denotes Q := by
  simp [denoteDiff, Set.diff_eq_empty]

/-- Adding constraints to P shrinks the difference. -/
theorem denoteDiff_antitone_left {P₁ P₂ : Program} (h : P₁ ⊆ P₂) (Q : Program) :
    denoteDiff P₂ Q ⊆ denoteDiff P₁ Q :=
  Set.diff_subset_diff_left (monotonicity h)

/-- Adding constraints to Q enlarges the difference (⟦Q⟧ shrinks,
    so less is subtracted). -/
theorem denoteDiff_antitone_right {Q₁ Q₂ : Program} (h : Q₁ ⊆ Q₂) (P : Program) :
    denoteDiff P Q₁ ⊆ denoteDiff P Q₂ :=
  Set.diff_subset_diff_right (monotonicity h)

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
theorem pure_neg_complement_inter (c : Constraint) :
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
theorem orientation_always_never_unsat (P : Program) (X : Selector₂) (d : Direction)
    (hA : ⟨.orientation X d, .always⟩ ∈ P)
    (hN : ⟨.orientation X d, .never⟩ ∈ P) :
    denotes P = ∅ :=
  always_never_unsat P (.orientation X d) hA hN

--------------------------------------------------------------------------------
-- Set Difference Decomposition
--------------------------------------------------------------------------------

/-- Finset-level program difference: ⟦P \ Q⟧ ⊇ ⟦P⟧.
    Removing constraints from P weakens the program. -/
theorem denotes_sdiff_supset (P Q : Program) : denotes P ⊆ denotes (P \ Q) :=
  monotonicity Finset.sdiff_subset

/-- The denotation set-difference is contained in the program-difference
    denotation: ⟦P⟧ \ ⟦Q⟧ ⊆ ⟦P \ Q⟧. -/
theorem denoteDiff_sub_sdiff (P Q : Program) : denoteDiff P Q ⊆ denotes (P \ Q) :=
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
theorem denoteDiff_approx (P Q : Program) (q : QualifiedConstraint)
    (hq : q ∈ Q) :
    denotes (P ∪ {flipMode q}) ⊆ denoteDiff P Q := by
  intro R hR
  refine ⟨monotonicity Finset.subset_union_left hR, ?_⟩
  intro ⟨_, hSatQ⟩
  obtain ⟨_, hSatPF⟩ := hR
  have hFlip := hSatPF (flipMode q) (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
  exact ((flipMode_neg q R).mp hFlip) (hSatQ q hq)

/-- **Existence of a program under-approximating set difference.**
    For any programs P and Q with q ∈ Q, there exists a program M whose
    denotation is contained in ⟦P⟧ \ ⟦Q⟧. Direct corollary of
    `denoteDiff_approx`. -/
theorem denoteDiff_witness (P Q : Program)
    (q : QualifiedConstraint) (hq : q ∈ Q) :
    ∃ M : Program, denotes M ⊆ denoteDiff P Q :=
  ⟨P ∪ {flipMode q}, denoteDiff_approx P Q q hq⟩


#check refinement
#check monotonicity
#check unsat_iff_empty
#check denoteDiff
#check denoteDiff_empty_iff
#check denoteDiff_decompose
#check compose_eq_inter
#check always_never_unsat
#check pure_neg_complement_inter
#check orientation_always_never_unsat

end Spytial
