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
/--
For a fixed key atom `a`, `fiber X a` is the unary selector of all atoms `b`
such that `(a, b) ∈ X`.
-/
def fiber (X : Selector₂) (a : Atom) : Selector₁ := (X.filter fun p => p.1 = a).image Prod.snd

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

/-- Negated keyed grouping is checked fiberwise: for each key `a`, no
    boundary can contain exactly the atoms in `fiber X a`.  This is
    strictly stronger than `¬ sat_group₂_core` (which only requires
    that no single *family* works for all keys simultaneously). -/
def sat_neg_group₂_core (R : Realization) (X : Selector₂) : Prop :=
  ∀ a ∈ firstOf X, ¬ sat_group₁_core R (fiber X a)

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
    Negation is the precise logical ¬ of the positive predicate,
    except for `group₂` which uses fiberwise negation (each key's
    group independently fails). -/
def modelsNegC (R : Realization) : Constraint → Prop
| .group₂ X _ => sat_neg_group₂_core R X
| c           => ¬ modelsC R c

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


/-- For a program `P`, `Gs` lists all group boundaries actually used by its
    positive group constraints.  Negated groups do not contribute boundaries;
    they assert non-existence via `modelsNegC`. -/
def groupWitnesses (R : Realization) (P : Program) (Gs : Finset GroupBoundary) : Prop :=
  (∀ S,      (⟨Constraint.group₁ S, .always⟩ : QualifiedConstraint) ∈ P →
     ∃ g ∈ Gs, ∀ a, ((∃ b, R a = some b ∧ contains g b) ↔ a ∈ S)) ∧
  (∀ X addE, (⟨Constraint.group₂ X addE, .always⟩ : QualifiedConstraint) ∈ P →
     ∃ fam : Atom → GroupBoundary,
       (∀ a ∈ firstOf X, fam a ∈ Gs) ∧
       (∀ a ∈ firstOf X, ∀ b, ((∃ bb, R b = some bb ∧ contains (fam a) bb) ↔ (a,b) ∈ X)))

/-- Program satisfaction: keep per-constraint rules, add a single global `Gs`. -/
def modelsP (R : Realization) (P : Program) : Prop :=
  ∃ Gs : Finset GroupBoundary,
    groupWitnesses R P Gs ∧
    groupsSubsumptionGlobal R Gs ∧
    (∀ c ∈ P, modelsQC R c)

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
Adding a qualified constraint refines the denotation (shrinks the set).
-/
theorem refinement (P : Program) (C : QualifiedConstraint) :
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

/-- Composition (program union) refines both components: its denotation is
    contained in the intersection of the individual denotations.

    The reverse inclusion does not hold in general because merging group
    boundary witnesses from two programs may violate `groupsSubsumptionGlobal`. -/
theorem compose_sub_inter (P Q : Program) :
    denotes (compose P Q) ⊆ denotes P ∩ denotes Q :=
  fun _ hR => ⟨monotonicity Finset.subset_union_left hR,
               monotonicity Finset.subset_union_right hR⟩

--------------------------------------------------------------------------------
-- Pure Negation: Contradiction and Complement
--------------------------------------------------------------------------------

/-- A constraint has *pure negation* when `holds: never` is exactly the
    logical negation of `holds: always`.  This holds for every constraint
    except `group₂`, which uses fiberwise negation (strictly stronger). -/
def has_pure_negation (c : Constraint) : Prop :=
  ∀ R : Realization, modelsNegC R c ↔ ¬ modelsC R c

lemma orientation_pure_neg (X : Selector₂) (d : Direction) :
    has_pure_negation (.orientation X d) := fun _ => Iff.rfl
lemma align_pure_neg (X : Selector₂) (a : AlignDir) :
    has_pure_negation (.align X a) := fun _ => Iff.rfl
lemma cyclic_pure_neg (X : Selector₂) (r : Rotation) :
    has_pure_negation (.cyclic X r) := fun _ => Iff.rfl
lemma group₁_pure_neg (S : Selector₁) : has_pure_negation (.group₁ S) := fun _ => Iff.rfl
lemma size_pure_neg (w h : ℚ) (S : Selector₁) : has_pure_negation (.size w h S) :=
  fun _ => Iff.rfl
lemma hideatom_pure_neg (S : Selector₁) : has_pure_negation (.hideatom S) :=
  fun _ => Iff.rfl

/-- Exhaustiveness: every realization satisfies one mode. -/
theorem pure_neg_exhaustive (c : Constraint) (hPure : has_pure_negation c)
    (R : Realization) : modelsC R c ∨ modelsNegC R c := by
  by_cases h : modelsC R c
  · exact Or.inl h
  · exact Or.inr ((hPure R).mpr h)

/-- Exclusivity: no realization satisfies both modes. -/
theorem pure_neg_exclusive (c : Constraint) (hPure : has_pure_negation c)
    (R : Realization) : ¬ (modelsC R c ∧ modelsNegC R c) :=
  fun ⟨hPos, hNeg⟩ => ((hPure R).mp hNeg) hPos

/-- A program with both `holds: always` and `holds: never` for a
    pure-negation constraint is unsatisfiable. -/
theorem always_never_unsat (P : Program) (c : Constraint)
    (hPure : has_pure_negation c)
    (hA : ⟨c, .always⟩ ∈ P) (hN : ⟨c, .never⟩ ∈ P) :
    denotes P = ∅ := by
  apply unsat_empty
  intro R _ ⟨_, _, _, hSat⟩
  exact pure_neg_exclusive c hPure R ⟨hSat _ hA, hSat _ hN⟩

/-- Complement intersection: ⟦{c, always}⟧ ∩ ⟦{c, never}⟧ = ∅. -/
theorem pure_neg_complement_inter (c : Constraint) (hPure : has_pure_negation c) :
    denotes {⟨c, .always⟩} ∩ denotes {⟨c, .never⟩} = ∅ := by
  ext R
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨hA, hN⟩
  simp only [denotes, modelsP, Set.mem_setOf] at hA hN
  obtain ⟨_, _, _, _, hSatA⟩ := hA
  obtain ⟨_, _, _, _, hSatN⟩ := hN
  exact pure_neg_exclusive c hPure R
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
  always_never_unsat P (.orientation X d) (orientation_pure_neg X d) hA hN

--------------------------------------------------------------------------------
-- Group Subsumption Consequences
--------------------------------------------------------------------------------

/-- If two positive group₁ constraints have overlapping selectors (share
    at least one atom), then in any valid realization one selector is
    contained in the other.  This follows from the group subsumption
    discipline: boundaries that overlap on any box must be globally nested. -/
theorem group_overlap_nesting (P : Program) (S₁ S₂ : Selector₁)
    (hA₁ : ⟨.group₁ S₁, .always⟩ ∈ P)
    (hA₂ : ⟨.group₁ S₂, .always⟩ ∈ P)
    (hOv : (S₁ ∩ S₂).Nonempty)
    (R : Realization) (hR : R ∈ denotes P) :
    S₁ ⊆ S₂ ∨ S₂ ⊆ S₁ := by
  obtain ⟨_, Gs, hGW, hGSub, _⟩ := hR
  obtain ⟨g₁, hg₁_mem, hg₁⟩ := hGW.1 S₁ hA₁
  obtain ⟨g₂, hg₂_mem, hg₂⟩ := hGW.1 S₂ hA₂
  obtain ⟨c, hc⟩ := hOv
  rw [Finset.mem_inter] at hc
  -- The shared atom c has a box in both group boundaries
  obtain ⟨bc₁, hRc₁, hcont₁⟩ := (hg₁ c).mpr hc.1
  obtain ⟨bc₂, hRc₂, hcont₂⟩ := (hg₂ c).mpr hc.2
  have hbc : bc₁ = bc₂ := by simpa using hRc₁.symm.trans hRc₂
  subst hbc
  by_cases hg : g₁ = g₂
  · -- Same boundary ⟹ same selector ⟹ S₁ ⊆ S₂
    left; intro a ha
    obtain ⟨ba, hRa, hconta⟩ := (hg₁ a).mpr ha
    exact (hg₂ a).mp ⟨ba, hRa, hg ▸ hconta⟩
  · -- Different boundaries sharing a box ⟹ subsumption gives nesting
    rcases hGSub g₁ g₂ hg hg₁_mem hg₂_mem ⟨c, bc₁, hRc₁, hcont₁, hcont₂⟩ with h | h
    · left; intro a ha
      obtain ⟨ba, hRa, hconta⟩ := (hg₁ a).mpr ha
      exact (hg₂ a).mp ⟨ba, hRa, h a ba hRa hconta⟩
    · right; intro a ha
      obtain ⟨ba, hRa, hconta⟩ := (hg₂ a).mpr ha
      exact (hg₁ a).mp ⟨ba, hRa, h a ba hRa hconta⟩

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

lemma flipMode_constraint (q : QualifiedConstraint) :
    (flipMode q).constraint = q.constraint := by
  rcases q with ⟨c, (_ | _)⟩ <;> rfl

/-- Flipping mode negates satisfaction for pure-negation constraints. -/
lemma flipMode_neg (q : QualifiedConstraint)
    (hPure : has_pure_negation q.constraint) (R : Realization) :
    modelsQC R (flipMode q) ↔ ¬ modelsQC R q := by
  rcases q with ⟨c, (_ | _)⟩
  · exact hPure R
  · exact ((not_congr (hPure R)).trans not_not).symm

/-- A constraint is a group constraint (group₁ or group₂). -/
def Constraint.isGroup : Constraint → Prop
| .group₁ _ => True
| .group₂ _ _ => True
| _ => False

/-- A program is group-free if it contains no group constraints. -/
def groupFree (Q : Program) : Prop := ∀ q ∈ Q, ¬ Constraint.isGroup q.constraint

/-- All constraints in a group-free program have pure negation. -/
lemma groupFree_pure_neg {Q : Program} (hGF : groupFree Q)
    {q : QualifiedConstraint} (hq : q ∈ Q) :
    has_pure_negation q.constraint := by
  have := hGF q hq
  rcases q with ⟨c, _⟩
  cases c <;> simp [Constraint.isGroup] at this <;> exact fun _ => Iff.rfl

/-- For group-free programs, satisfaction reduces to per-constraint satisfaction
    (the group witness existential is trivially satisfied by `Gs = ∅`). -/
lemma groupFree_modelsP (R : Realization) (Q : Program) (hGF : groupFree Q) :
    modelsP R Q ↔ ∀ q ∈ Q, modelsQC R q := by
  constructor
  · exact fun ⟨_, _, _, hSat⟩ => hSat
  · intro hSat
    exact ⟨∅,
      ⟨fun S hS => absurd (show Constraint.isGroup (.group₁ S) from trivial) (hGF _ hS),
       fun X addE hX => absurd (show Constraint.isGroup (.group₂ X addE) from trivial) (hGF _ hX)⟩,
      fun _ _ _ hg₁ => absurd hg₁ (Finset.notMem_empty _),
      hSat⟩

/-- Group witnesses extend from P to P ∪ {q} when q is not a group constraint. -/
lemma groupWitnesses_insert {R : Realization} {P : Program} {Gs : Finset GroupBoundary}
    (q : QualifiedConstraint) (hGW : groupWitnesses R P Gs)
    (hng : ¬ Constraint.isGroup q.constraint) :
    groupWitnesses R (P ∪ {q}) Gs := by
  constructor
  · intro S hS
    rcases Finset.mem_union.mp hS with h | h
    · exact hGW.1 S h
    · exact absurd (Finset.mem_singleton.mp h ▸ show Constraint.isGroup (.group₁ S) from trivial) hng
  · intro X addE hX
    rcases Finset.mem_union.mp hX with h | h
    · exact hGW.2 X addE h
    · exact absurd (Finset.mem_singleton.mp h ▸ show Constraint.isGroup (.group₂ X addE) from trivial) hng

/-- **Set difference decomposition.** For group-free Q:

    ⟦P⟧ \ ⟦Q⟧ = ⋃ q ∈ Q, ⟦P ∪ {flipMode q}⟧

    Each summand adds the negation of one specific constraint from Q.
    This shows that the denotation algebra is closed under set difference
    up to finite union (which programs cannot express internally, since
    programs are conjunctive). -/
theorem denoteDiff_decompose (P Q : Program) (hGF : groupFree Q) :
    denoteDiff P Q = ⋃ q ∈ Q, denotes (P ∪ {flipMode q}) := by
  ext R
  simp only [denoteDiff, Set.mem_diff, Set.mem_iUnion₂]
  constructor
  · -- Forward: R ∈ ⟦P⟧ ∧ R ∉ ⟦Q⟧ → ∃ q ∈ Q, R ∈ ⟦P ∪ {flipMode q}⟧
    intro ⟨hRP, hRQ⟩
    have hWF : R ∈ WF := hRP.1
    have hNMQ : ¬ modelsP R Q := fun h => hRQ ⟨hWF, h⟩
    rw [groupFree_modelsP R Q hGF] at hNMQ; push_neg at hNMQ
    obtain ⟨q, hqQ, hNeg⟩ := hNMQ
    obtain ⟨Gs, hGW, hGSub, hSat⟩ := hRP.2
    refine ⟨q, hqQ, hWF, Gs,
      groupWitnesses_insert _ hGW (flipMode_constraint q ▸ hGF q hqQ), hGSub, ?_⟩
    intro c hc
    rcases Finset.mem_union.mp hc with hP | hF
    · exact hSat c hP
    · rw [Finset.mem_singleton.mp hF]
      exact (flipMode_neg q (groupFree_pure_neg hGF hqQ) R).mpr hNeg
  · -- Reverse: ∃ q ∈ Q, R ∈ ⟦P ∪ {flipMode q}⟧ → R ∈ ⟦P⟧ ∧ R ∉ ⟦Q⟧
    intro ⟨q, hqQ, hWF, Gs, hGW, hGSub, hSat⟩
    refine ⟨⟨hWF, Gs, ⟨fun S hS => hGW.1 S (Finset.mem_union_left _ hS),
      fun X addE hX => hGW.2 X addE (Finset.mem_union_left _ hX)⟩,
      hGSub, fun c hc => hSat c (Finset.mem_union_left _ hc)⟩, ?_⟩
    intro ⟨_, hMQ⟩
    rw [groupFree_modelsP R Q hGF] at hMQ
    have hFlip := hSat (flipMode q) (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
    rw [flipMode_neg q (groupFree_pure_neg hGF hqQ) R] at hFlip
    exact hFlip (hMQ q hqQ)

/-- **Under-approximation of set difference.** For any q ∈ Q with pure
    negation, ⟦P ∪ {flipMode q}⟧ ⊆ ⟦P⟧ \ ⟦Q⟧.

    Unlike `denoteDiff_decompose`, this requires NO `groupFree` condition.
    If R satisfies flip(q), it violates q, so `modelsP R Q` fails regardless
    of whether Q's group subsumption holds.

    **Significance for the solver.** Spytial programs generally contain group
    constraints, so `denoteDiff_decompose` (which assumes `groupFree Q`) does
    not directly apply. This theorem fills that gap: given *any* programs P
    and Q and a non-group constraint q ∈ Q, the program `P ∪ {flipMode q}`
    is a *sound* (but incomplete) witness for the set difference ⟦P⟧ \ ⟦Q⟧.

    Concretely, to under-approximate ⟦P⟧ \ ⟦Q⟧ the solver can enumerate the
    non-group constraints q ∈ Q, flip each one, and solve `P ∪ {flipMode q}`.
    Every solution found this way is guaranteed to satisfy P but violate Q.
    Completeness is lost only for realizations that satisfy every non-group
    constraint in Q yet violate Q solely through group subsumption failure — a
    scenario that cannot arise when Q is group-free (hence the exact equality
    in `denoteDiff_decompose`). -/
theorem denoteDiff_approx (P Q : Program) (q : QualifiedConstraint)
    (hq : q ∈ Q) (hPure : has_pure_negation q.constraint) :
    denotes (P ∪ {flipMode q}) ⊆ denoteDiff P Q := by
  intro R hR
  refine ⟨monotonicity Finset.subset_union_left hR, ?_⟩
  intro ⟨_, _, _, _, hSatQ⟩
  obtain ⟨_, _, _, _, hSatPF⟩ := hR
  have hFlip := hSatPF (flipMode q) (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
  exact ((flipMode_neg q hPure R).mp hFlip) (hSatQ q hq)

/-- **Existence of a program under-approximating set difference.**
    For any programs P and Q, as long as Q contains at least one constraint
    with pure negation, there exists a program M whose denotation is contained
    in ⟦P⟧ \ ⟦Q⟧. Direct corollary of `denoteDiff_approx`. -/
theorem denoteDiff_witness (P Q : Program)
    (q : QualifiedConstraint) (hq : q ∈ Q)
    (hPure : has_pure_negation q.constraint) :
    ∃ M : Program, denotes M ⊆ denoteDiff P Q :=
  ⟨P ∪ {flipMode q}, denoteDiff_approx P Q q hq hPure⟩

#check refinement
#check monotonicity
#check unsat_iff_empty
#check denoteDiff
#check denoteDiff_empty_iff
#check denoteDiff_decompose
#check compose_sub_inter
#check always_never_unsat
#check pure_neg_complement_inter
#check orientation_always_never_unsat
#check group_overlap_nesting

end Spytial
