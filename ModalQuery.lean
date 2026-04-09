/-
# Modal Spatial Query Language

Formalizes the modal spatial query language from the diagram REPL.

The key idea is *Kripke-style* possible-worlds semantics where the
possible worlds are the well-formed realizations in the denotation ⟦P⟧
of a constraint program P.  The three modal operators quantify over
these worlds:

  * **must φ**   — φ holds in *every*  realization of ⟦P⟧  (necessity)
  * **can φ**    — φ holds in *some*   realization of ⟦P⟧  (possibility)
  * **cannot φ** — φ holds in *no*     realization of ⟦P⟧  (impossibility)

Queries return sets of atoms and compose via union, intersection, and
complement, mirroring the REPL syntax `union(...)`, `inter(...)`, `not(...)`.
-/

import Main

open Spytial

namespace Spytial

--------------------------------------------------------------------------------
-- Spatial Relations
--------------------------------------------------------------------------------

/-- The six spatial relations available in the REPL query language.
    These correspond to `must.leftOf(ref)`, `can.aligned.x(ref)`, etc. -/
inductive SpatialRel
  | leftOf | rightOf | above | below | alignedX | alignedY
deriving DecidableEq, Repr

/-- Lift a box-level spatial relation to a proposition about two atoms in a
    realization.  `atomRel R rel a ref` holds when R assigns boxes to both
    `a` and `ref` and the spatial relationship holds between them.

    For the REPL query `must.leftOf(B)`, this is evaluated as
    `atomRel R .leftOf a B` for each candidate atom `a`. -/
def atomRel (R : Realization) : SpatialRel → Atom → Atom → Prop
  | .leftOf,   a, ref => ∃ ba bref, R a = some ba ∧ R ref = some bref ∧ leftOf ba bref
  | .rightOf,  a, ref => ∃ ba bref, R a = some ba ∧ R ref = some bref ∧ leftOf bref ba
  | .above,    a, ref => ∃ ba bref, R a = some ba ∧ R ref = some bref ∧ Spytial.above ba bref
  | .below,    a, ref => ∃ ba bref, R a = some ba ∧ R ref = some bref ∧ Spytial.above bref ba
  | .alignedX, a, ref => ∃ ba bref, R a = some ba ∧ R ref = some bref ∧ aligned_v ba bref
  | .alignedY, a, ref => ∃ ba bref, R a = some ba ∧ R ref = some bref ∧ aligned_h ba bref

/-- Map the basic four `Direction` constructors to `SpatialRel`.
    The `directly*` variants combine direction + alignment and are not
    directly expressible as a single `SpatialRel`. -/
def directionToRel : Direction → SpatialRel
  | .left  => .leftOf
  | .right => .rightOf
  | .above => .above
  | .below => .below
  | .directlyLeft  => .leftOf
  | .directlyRight => .rightOf
  | .directlyAbove => .above
  | .directlyBelow => .below

/-- `rightOf` is the flip of `leftOf`. -/
theorem atomRel_rightOf_eq_flip (R : Realization) (a ref : Atom) :
    atomRel R .rightOf a ref ↔ atomRel R .leftOf ref a := by
  constructor
  · rintro ⟨ba, bref, ha, href, h⟩; exact ⟨bref, ba, href, ha, h⟩
  · rintro ⟨ba, bref, ha, href, h⟩; exact ⟨bref, ba, href, ha, h⟩

/-- `below` is the flip of `above`. -/
theorem atomRel_below_eq_flip (R : Realization) (a ref : Atom) :
    atomRel R .below a ref ↔ atomRel R .above ref a := by
  constructor
  · rintro ⟨ba, bref, ha, href, h⟩; exact ⟨bref, ba, href, ha, h⟩
  · rintro ⟨ba, bref, ha, href, h⟩; exact ⟨bref, ba, href, ha, h⟩

--------------------------------------------------------------------------------
-- Modal Operators
--------------------------------------------------------------------------------

/-- Necessarily: the spatial relation holds for atom `a` (relative to `ref`)
    in *every* realization satisfying program P. -/
def must (P : Program) (rel : SpatialRel) (ref a : Atom) : Prop :=
  ∀ R ∈ denotes P, atomRel R rel a ref

/-- Possibly: the spatial relation holds for atom `a` (relative to `ref`)
    in *some* realization satisfying program P. -/
def can (P : Program) (rel : SpatialRel) (ref a : Atom) : Prop :=
  ∃ R ∈ denotes P, atomRel R rel a ref

/-- Impossibly: the spatial relation holds for atom `a` (relative to `ref`)
    in *no* realization satisfying program P. -/
def cannot (P : Program) (rel : SpatialRel) (ref a : Atom) : Prop :=
  ¬ ∃ R ∈ denotes P, atomRel R rel a ref

/-- The set of atoms that *must* satisfy a relation w.r.t. `ref`. -/
def mustSet (P : Program) (rel : SpatialRel) (ref : Atom) : Set Atom :=
  { a | must P rel ref a }

/-- The set of atoms that *can* satisfy a relation w.r.t. `ref`. -/
def canSet (P : Program) (rel : SpatialRel) (ref : Atom) : Set Atom :=
  { a | can P rel ref a }

/-- The set of atoms that *cannot* satisfy a relation w.r.t. `ref`. -/
def cannotSet (P : Program) (rel : SpatialRel) (ref : Atom) : Set Atom :=
  { a | cannot P rel ref a }

--------------------------------------------------------------------------------
-- Basic Modal Identities
--------------------------------------------------------------------------------

/-- `cannot` is definitionally the negation of `can`. -/
theorem cannot_eq_not_can (P : Program) (rel : SpatialRel) (ref a : Atom) :
    cannot P rel ref a ↔ ¬ can P rel ref a :=
  Iff.rfl

/-- Necessity implies possibility, provided the denotation is nonempty
    (i.e., the program is satisfiable). -/
theorem must_implies_can (P : Program) (rel : SpatialRel) (ref a : Atom)
    (hNE : (denotes P).Nonempty)
    (hMust : must P rel ref a) : can P rel ref a := by
  obtain ⟨R, hR⟩ := hNE
  exact ⟨R, hR, hMust R hR⟩

/-- `cannotSet` is the set-complement of `canSet`. -/
theorem cannotSet_eq_compl_canSet (P : Program) (rel : SpatialRel) (ref : Atom) :
    cannotSet P rel ref = (canSet P rel ref)ᶜ := by
  ext a; simp [cannotSet, canSet, cannot, can]

/-- `mustSet ⊆ canSet` when the program is satisfiable. -/
theorem mustSet_sub_canSet (P : Program) (rel : SpatialRel) (ref : Atom)
    (hNE : (denotes P).Nonempty) :
    mustSet P rel ref ⊆ canSet P rel ref := by
  intro a ha
  exact must_implies_can P rel ref a hNE ha

/-- `mustSet` and `cannotSet` are disjoint when the program is satisfiable.
    (When `⟦P⟧ = ∅`, both `must` and `cannot` hold vacuously for all atoms.) -/
theorem mustSet_disjoint_cannotSet (P : Program) (rel : SpatialRel) (ref : Atom)
    (hNE : (denotes P).Nonempty) :
    mustSet P rel ref ∩ cannotSet P rel ref = ∅ := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨hMust, hCannot⟩
  exact hCannot (must_implies_can P rel ref a hNE hMust)

--------------------------------------------------------------------------------
-- Monotonicity
--------------------------------------------------------------------------------

/-- More constraints produce more necessities: adding constraints shrinks the
    set of possible worlds, so any property that held in all worlds still does.

    Uses `antimonotonicity` from Main.lean: `P ⊆ Q → ⟦Q⟧ ⊆ ⟦P⟧`. -/
theorem must_monotone (P Q : Program) (rel : SpatialRel) (ref : Atom)
    (hPQ : P ⊆ Q) :
    mustSet P rel ref ⊆ mustSet Q rel ref := by
  intro a ha
  simp only [mustSet, Set.mem_setOf_eq, must] at *
  intro R hR
  exact ha R (antimonotonicity hPQ hR)

/-- More constraints reduce possibilities: adding constraints shrinks
    the set of possible worlds, so fewer atoms can satisfy a relation.

    Contravariant in program inclusion. -/
theorem can_antitone (P Q : Program) (rel : SpatialRel) (ref : Atom)
    (hPQ : P ⊆ Q) :
    canSet Q rel ref ⊆ canSet P rel ref := by
  intro a ha
  simp only [canSet, Set.mem_setOf_eq, can] at *
  obtain ⟨R, hR, hRel⟩ := ha
  exact ⟨R, antimonotonicity hPQ hR, hRel⟩

/-- More constraints expand impossibilities. -/
theorem cannot_monotone (P Q : Program) (rel : SpatialRel) (ref : Atom)
    (hPQ : P ⊆ Q) :
    cannotSet P rel ref ⊆ cannotSet Q rel ref := by
  rw [cannotSet_eq_compl_canSet, cannotSet_eq_compl_canSet]
  exact Set.compl_subset_compl.mpr (can_antitone P Q rel ref hPQ)

--------------------------------------------------------------------------------
-- Query Language
--------------------------------------------------------------------------------

/-- Modal operator tag, mirroring the REPL's three quantifiers. -/
inductive Modality
  | must | can | cannot
deriving DecidableEq, Repr

/-- AST for spatial queries.  Mirrors the PEG grammar in
    `spytial-core/src/evaluators/layout/layout-query.pegjs`. -/
inductive Query where
  | modal   : Modality → SpatialRel → Atom → Query
  | union   : Query → Query → Query
  | inter   : Query → Query → Query
  | compl   : Query → Query
  | grouped : Atom → Query

/-- Evaluate a query to the set of atoms it selects.

    `allAtoms` is the universe of atoms in the diagram (needed for
    complement).  `groups` maps each atom to its group membership set. -/
def evalQuery (P : Program) (allAtoms : Set Atom)
    (groups : Atom → Set Atom) : Query → Set Atom
  | .modal .must   rel ref => mustSet P rel ref
  | .modal .can    rel ref => canSet P rel ref
  | .modal .cannot rel ref => cannotSet P rel ref
  | .union q₁ q₂  => evalQuery P allAtoms groups q₁ ∪ evalQuery P allAtoms groups q₂
  | .inter q₁ q₂  => evalQuery P allAtoms groups q₁ ∩ evalQuery P allAtoms groups q₂
  | .compl q       => allAtoms \ evalQuery P allAtoms groups q
  | .grouped a     => groups a

--------------------------------------------------------------------------------
-- Set Operation Properties
--------------------------------------------------------------------------------

@[simp] theorem evalQuery_union (P : Program) (u : Set Atom) (g : Atom → Set Atom)
    (q₁ q₂ : Query) :
    evalQuery P u g (.union q₁ q₂) = evalQuery P u g q₁ ∪ evalQuery P u g q₂ :=
  rfl

@[simp] theorem evalQuery_inter (P : Program) (u : Set Atom) (g : Atom → Set Atom)
    (q₁ q₂ : Query) :
    evalQuery P u g (.inter q₁ q₂) = evalQuery P u g q₁ ∩ evalQuery P u g q₂ :=
  rfl

@[simp] theorem evalQuery_compl (P : Program) (u : Set Atom) (g : Atom → Set Atom)
    (q : Query) :
    evalQuery P u g (.compl q) = u \ evalQuery P u g q :=
  rfl

/-- Double complement restores the original query result
    (when restricted to `allAtoms`). -/
theorem evalQuery_compl_compl (P : Program) (u : Set Atom) (g : Atom → Set Atom)
    (q : Query)
    (hSub : evalQuery P u g q ⊆ u) :
    evalQuery P u g (.compl (.compl q)) = evalQuery P u g q := by
  simp [Set.diff_diff_cancel_left hSub]

--------------------------------------------------------------------------------
-- Connection to HoldsMode
--------------------------------------------------------------------------------

/-- An always-orientation constraint entails `must` for every pair in the
    selector.  This bridges the static constraint system (Main.lean) with
    the modal query language.

    The pair convention in `sat_orientation` is `(ref, a)`: the first
    element is the reference point, the second is the constrained atom.
    So `(ref, a) ∈ X` with `Direction.left` means "a is to the left of ref". -/
theorem always_orientation_implies_must
    (P : Program) (X : Selector₂) (d : Direction) (ref a : Atom)
    (hIn : ⟨.orientation X d, .always⟩ ∈ P)
    (hPair : (ref, a) ∈ X)
    (hBasic : d = .left ∨ d = .right ∨ d = .above ∨ d = .below) :
    must P (directionToRel d) ref a := by
  intro R ⟨_, hModels⟩
  have hSat := hModels ⟨.orientation X d, .always⟩ hIn
  simp only [modelsQC, modelsC] at hSat
  rcases hBasic with rfl | rfl | rfl | rfl
  all_goals {
    simp only [sat_orientation, lift₂] at hSat
    obtain ⟨bref, ba, href, ha, hRel⟩ := hSat hPair
    simp only [atomRel, directionToRel]
    exact ⟨ba, bref, ha, href, hRel⟩
  }

/-!
### Note on `never` and `cannot`

`holds: never` means `¬ sat_orientation R X d`, i.e., there exists some
pair in X for which the relation fails.  This is weaker than saying
*every* pair fails.  For a singleton selector `{(a, ref)}`, the
equivalence is exact, and `never` does imply `cannot`.
-/

/-- For singleton selectors, `holds: never` implies `cannot`. -/
theorem never_orientation_singleton_implies_cannot
    (P : Program) (d : Direction) (ref a : Atom)
    (hIn : ⟨.orientation {(ref, a)} d, .never⟩ ∈ P)
    (hBasic : d = .left ∨ d = .right ∨ d = .above ∨ d = .below) :
    cannot P (directionToRel d) ref a := by
  intro ⟨R, ⟨_, hModels⟩, hRel⟩
  have hSat := hModels ⟨.orientation {(ref, a)} d, .never⟩ hIn
  simp only [modelsQC, modelsNegC, modelsC] at hSat
  apply hSat
  rcases hBasic with rfl | rfl | rfl | rfl
  all_goals {
    simp only [atomRel, directionToRel] at hRel
    obtain ⟨ba, bref, ha, href, hBoxRel⟩ := hRel
    simp only [sat_orientation, lift₂]
    intro ref' a' hPair'
    simp only [Finset.mem_singleton, Prod.mk.injEq] at hPair'
    obtain ⟨rfl, rfl⟩ := hPair'
    exact ⟨bref, ba, href, ha, hBoxRel⟩
  }

--------------------------------------------------------------------------------
-- Summary of Main Theorems
--------------------------------------------------------------------------------

-- Basic Modal Identities
#check @cannot_eq_not_can          -- cannot ↔ ¬ can
#check @must_implies_can           -- must → can  (when ⟦P⟧ ≠ ∅)
#check @cannotSet_eq_compl_canSet  -- cannotSet = (canSet)ᶜ
#check @mustSet_sub_canSet         -- mustSet ⊆ canSet  (when ⟦P⟧ ≠ ∅)
#check @mustSet_disjoint_cannotSet -- must ∩ cannot = ∅

-- Monotonicity
#check @must_monotone              -- P ⊆ Q → mustSet P ⊆ mustSet Q
#check @can_antitone               -- P ⊆ Q → canSet Q ⊆ canSet P
#check @cannot_monotone            -- P ⊆ Q → cannotSet P ⊆ cannotSet Q

-- Set Operations
#check @evalQuery_union            -- eval(union q₁ q₂) = eval(q₁) ∪ eval(q₂)
#check @evalQuery_inter            -- eval(inter q₁ q₂) = eval(q₁) ∩ eval(q₂)
#check @evalQuery_compl            -- eval(not q) = U \ eval(q)
#check @evalQuery_compl_compl      -- eval(not(not q)) = eval(q)

-- Connection to Constraint System
#check @always_orientation_implies_must           -- holds:always → must
#check @never_orientation_singleton_implies_cannot -- holds:never (singleton) → cannot

end Spytial
