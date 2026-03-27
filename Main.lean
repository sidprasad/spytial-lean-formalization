/-
# Spytial: Spatial Semantics
* A program is a finite set of spytial constraints.
* Its denotation is the set of realizations (layouts)
* that satisfy those constraints.
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

--------------------------------------------------------------------------------
-- Constraint Satisfaction Rules
--------------------------------------------------------------------------------


def sat_size (R : Realization) (w h : ℚ) (S : Selector₁) : Prop :=
  lift₁ R S (fun b => b.width = w ∧ b.height = h)

def sat_hide (R : Realization) (S : Selector₁) : Prop :=
  ∀ a ∈ S, R a = none

def sat_orientation (R : Realization) : Selector₂ → Direction → Prop
| X, .left            => lift₂ R X leftOf
| X, .right           => lift₂ R X (fun b₁ b₂ => leftOf b₂ b₁)
| X, .above           => lift₂ R X above
| X, .below           => lift₂ R X (fun b₁ b₂ => above b₂ b₁)
| X, .directlyLeft    => lift₂ R X (fun b₁ b₂ => leftOf b₁ b₂ ∧ aligned_h b₁ b₂)
| X, .directlyRight   => lift₂ R X (fun b₁ b₂ => leftOf b₂ b₁ ∧ aligned_h b₁ b₂)
| X, .directlyAbove   => lift₂ R X (fun b₁ b₂ => above  b₁ b₂ ∧ aligned_v b₁ b₂)
| X, .directlyBelow   => lift₂ R X (fun b₁ b₂ => above  b₂ b₁ ∧ aligned_v b₁ b₂)


def sat_align (R : Realization) : Selector₂ → AlignDir → Prop
| X, .horizontal => lift₂ R X aligned_h
| X, .vertical   => lift₂ R X aligned_v


--------------------------
-- Groups
--------------------------

/-- Subsumption discipline. If two groups ever overlap in a realized box,
    then one must globally contain the other across all boxes. -/
def groupsSubsumptionGlobal (R : Realization) (Gs : Finset GroupBoundary) : Prop :=
  ∀ g₁ g₂, g₁ ≠ g₂ → g₁ ∈ Gs → g₂ ∈ Gs →
    ( (∃ b bb, R b = some bb ∧ contains g₁ bb ∧ contains g₂ bb) →
      ( (∀ b bb, R b = some bb → contains g₁ bb → contains g₂ bb) ∨
        (∀ b bb, R b = some bb → contains g₂ bb → contains g₁ bb) ) )

/-- Unary grouping core (GRP1): one boundary contains exactly the selected atoms' boxes. -/
def sat_group₁_core (R : Realization) (S : Selector₁) : Prop :=
  ∃ g : GroupBoundary,
    ∀ a, ((∃ b, R a = some b ∧ contains g b) ↔ a ∈ S)



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

/-- Contiguous subpath relation X ⊑ Y with properness (|X| < |Y|). -/
def contigSubpath (X Y : List Atom) : Prop :=
  X.length < Y.length ∧ ∃ j, X = (Y.drop j).take X.length

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
    ∃ k, k < L.length ∧ allPairs_ok R L k

/-- Counterclockwise: reuse clockwise on reversed lists. -/
noncomputable def sat_cyclic_ccw (R : Realization) (X : Selector₂) : Prop :=
  ∀ L ∈ maximalSimplePaths X,
    let L' := L.reverse
    ∃ k, k < L'.length ∧ allPairs_ok R L' k

/-- Unified API as in your constraint syntax. -/
noncomputable def sat_cyclic (R : Realization) (X : Selector₂) (rot : Rotation) : Prop :=
  match rot with
  | .clockwise        => sat_cyclic_cw  R X
  | .counterclockwise => sat_cyclic_ccw R X

/-- Per-constraint satisfaction predicate. -/
def modelsC (R : Realization) : Constraint → Prop
| .orientation X d => sat_orientation      R X d
| .align       X a => sat_align       R X a
| .size  w h   S   => sat_size        R w h S
| .hideatom    S   => sat_hide        R S
| .group₁      S   => sat_group₁_core R S
| .group₂      X _ => sat_group₂_core R X
| .cyclic      X r => sat_cyclic      R X r





--------- Semantics ---------

/--
 From a spatial perspective, the semantics of a program (set of constraints)
 is the set of well-formed realizations that satisfy all its constraints.

 Program composition is set union.
 and a realization satisfies a program if it satisfies all its constraints.
-/

abbrev Program := Finset Constraint

def compose (P Q : Program) : Program := P ∪ Q


/-- For a program `P`, `Gs` lists all group boundaries actually used by its group constraints. -/
def groupWitnesses (R : Realization) (P : Program) (Gs : Finset GroupBoundary) : Prop :=
  (∀ S,      Constraint.group₁ S    ∈ P →
     ∃ g ∈ Gs, ∀ a, ((∃ b, R a = some b ∧ contains g b) ↔ a ∈ S)) ∧
  (∀ X addE, Constraint.group₂ X addE ∈ P →
     ∃ fam : Atom → GroupBoundary,
       (∀ a ∈ firstOf X, fam a ∈ Gs) ∧
       (∀ a ∈ firstOf X, ∀ b, ((∃ bb, R b = some bb ∧ contains (fam a) bb) ↔ (a,b) ∈ X)))

/-- Program satisfaction: keep per-constraint rules, add a single global `Gs`. -/
def modelsP (R : Realization) (P : Program) : Prop :=
  ∃ Gs : Finset GroupBoundary,
    groupWitnesses R P Gs ∧
    groupsSubsumptionGlobal R Gs ∧
    (∀ c ∈ P, modelsC R c)

--------------------------------------------------------------------------------
-- Denotational Semantics
--------------------------------------------------------------------------------


/--
The denotation of a *program* is the set of realizations
that satisfy all constraints in the program,
and are well-formed.
-/
def denotes (P : Finset Constraint) : Set Realization :=
  { R | R ∈ WF ∧ modelsP R P }

notation "⟦" P "⟧" => denotes P

lemma denotes_empty : ⟦∅⟧ = WF := by
  ext R
  simp only [denotes, modelsP, Set.mem_setOf]
  constructor
  · intro ⟨hWF, Gs, _, _, _⟩
    exact hWF
  · intro hWF
    use hWF
    use ∅
    simp [groupWitnesses, groupsSubsumptionGlobal]



--------------------------------------------------------------------------------
-- Key Meta Theorems
--------------------------------------------------------------------------------


/--
Adding a constraint refines the denotation (shrinks the set).
-/
theorem refinement (P : Program) (C : Constraint) :
  denotes (P ∪ {C}) ⊆ ⟦P⟧ := by
  intro R h
  simp only [denotes, modelsP] at h ⊢
  rcases h with ⟨hWF, Gs, hGW, hGSub, hSat⟩
  exact ⟨hWF, Gs, by
    constructor
    · intro S hS
      exact hGW.1 S (Finset.mem_union_left {C} hS)
    · intro X addE hX
      exact hGW.2 X addE (Finset.mem_union_left {C} hX)
  , hGSub, fun D hD => hSat D (Finset.mem_union_left {C} hD)⟩


/--
Corollary to `refinement`. If a program `P` is a subset of `Q`,
then the denotation of `Q` is a superset of the denotation of `P`.
-/
theorem monotonicity {P Q : Program} (hPQ : P ⊆ Q) : (denotes Q) ⊆ (denotes P) := by
  intro R hR
  simp only [denotes, modelsP] at *
  rcases hR with ⟨hWF, Gs, hGW, hGSub, hSatQ⟩
  exact ⟨hWF, Gs, by
    constructor
    · intro S hS
      exact hGW.1 S (hPQ hS)
    · intro X addE hX
      exact hGW.2 X addE (hPQ hX)
  , hGSub, fun D hDP => hSatQ D (hPQ hDP)⟩


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


#check refinement
#check monotonicity
#check unsat_iff_empty

end Spytial
