/-
# Abstract Solver Specification

Models the constraint-to-linear-inequality translation (corresponding to
`constraintToKiwi` in spytial-core) and proves soundness/completeness:

  * **Soundness**: any solution to the emitted linear system can be lifted
    to a realization in ⟦P⟧.
  * **Completeness**: if ⟦P⟧ ≠ ∅ then the emitted linear system is feasible.

We do NOT model the numeric solver (Kiwi.js / WebCola) — only the
translation from `Constraint` to linear inequalities over rationals.
-/

import Main

open Spytial

--------------------------------------------------------------------------------
-- Variable and Linear Inequality IR
--------------------------------------------------------------------------------

/-- Identifier for group bounding boxes. -/
structure GroupId where id : Nat
deriving BEq, DecidableEq, Hashable

/-- Variables in the emitted linear system.
    Each atom has an (x, y) coordinate; each group has four bounding-box edges. -/
inductive SolverVar where
  | x     : Atom → SolverVar
  | y     : Atom → SolverVar
  | gLeft : GroupId → SolverVar
  | gRight: GroupId → SolverVar
  | gTop  : GroupId → SolverVar
  | gBot  : GroupId → SolverVar
deriving DecidableEq

/-- Linear inequalities emitted by the translation.
    These mirror what `constraintToKiwi` produces in Kiwi.js. -/
inductive LinearIneq where
  | le  : SolverVar → ℚ → SolverVar → LinearIneq   -- v₁ + c ≤ v₂
  | eq  : SolverVar → SolverVar → LinearIneq         -- v₁ = v₂
  | geq : SolverVar → ℚ → SolverVar → LinearIneq   -- v₁ ≥ v₂ + c  (i.e. v₂ + c ≤ v₁)

/-- An assignment maps solver variables to rationals. -/
abbrev Assignment := SolverVar → ℚ

/-- Satisfaction of a single linear inequality under an assignment. -/
def satisfies_ineq (σ : Assignment) : LinearIneq → Prop
  | .le v₁ c v₂  => σ v₁ + c ≤ σ v₂
  | .eq v₁ v₂    => σ v₁ = σ v₂
  | .geq v₁ c v₂ => σ v₁ ≥ σ v₂ + c

/-- A system is feasible iff some assignment satisfies all inequalities. -/
def feasible (sys : List LinearIneq) : Prop :=
  ∃ σ : Assignment, ∀ ineq ∈ sys, satisfies_ineq σ ineq

/-- Strict satisfaction (for bridging the ≤ / < gap). -/
def satisfies_ineq_strict (σ : Assignment) : LinearIneq → Prop
  | .le v₁ c v₂  => σ v₁ + c < σ v₂
  | .eq v₁ v₂    => σ v₁ = σ v₂
  | .geq v₁ c v₂ => σ v₁ > σ v₂ + c

/-- Strict satisfaction implies non-strict. -/
lemma strict_implies_nonstrict (σ : Assignment) (ineq : LinearIneq) :
    satisfies_ineq_strict σ ineq → satisfies_ineq σ ineq := by
  cases ineq with
  | le v₁ c v₂ => exact le_of_lt
  | eq v₁ v₂ => exact id
  | geq v₁ c v₂ => exact le_of_lt

--------------------------------------------------------------------------------
-- Dimension Context
--------------------------------------------------------------------------------

/-- A dimension context assigns each atom a width and height (positive rationals).
    This mirrors the node dimensions known at constraint-emission time. -/
structure DimCtx where
  width  : Atom → ℚ
  height : Atom → ℚ
  width_pos  : ∀ a, 0 < width a
  height_pos : ∀ a, 0 < height a

--------------------------------------------------------------------------------
-- Translation: Constraint → List LinearIneq
--------------------------------------------------------------------------------

/-- Translate an orientation constraint to linear inequalities.
    Mirrors `constraint-validator.ts:1869–1911`. -/
noncomputable def translate_orientation (dims : DimCtx) (X : Selector₂) :
    Direction → List LinearIneq
  | .right        => X.toList.map fun (a, b) =>
      LinearIneq.le (.x a) (dims.width a) (.x b)
  | .left         => X.toList.map fun (a, b) =>
      LinearIneq.le (.x b) (dims.width b) (.x a)
  | .below        => X.toList.map fun (a, b) =>
      LinearIneq.le (.y a) (dims.height a) (.y b)
  | .above        => X.toList.map fun (a, b) =>
      LinearIneq.le (.y b) (dims.height b) (.y a)
  | .directlyRight => X.toList.flatMap fun (a, b) =>
      [LinearIneq.le (.x a) (dims.width a) (.x b),
       LinearIneq.eq (.y a) (.y b)]
  | .directlyLeft  => X.toList.flatMap fun (a, b) =>
      [LinearIneq.le (.x b) (dims.width b) (.x a),
       LinearIneq.eq (.y a) (.y b)]
  | .directlyBelow => X.toList.flatMap fun (a, b) =>
      [LinearIneq.le (.y a) (dims.height a) (.y b),
       LinearIneq.eq (.x a) (.x b)]
  | .directlyAbove => X.toList.flatMap fun (a, b) =>
      [LinearIneq.le (.y b) (dims.height b) (.y a),
       LinearIneq.eq (.x a) (.x b)]

/-- Translate an alignment constraint. -/
noncomputable def translate_align (X : Selector₂) : AlignDir → List LinearIneq
  | .horizontal => X.toList.map fun (a, b) => LinearIneq.eq (.y a) (.y b)
  | .vertical   => X.toList.map fun (a, b) => LinearIneq.eq (.x a) (.x b)

/-- Translate a unary group constraint (group₁) to bounding-box containment inequalities. -/
noncomputable def translate_group₁ (dims : DimCtx) (S : Selector₁) (gid : GroupId) :
    List LinearIneq :=
  S.toList.flatMap fun a =>
    [ LinearIneq.geq (.x a) 0 (.gLeft gid),
      LinearIneq.geq (.y a) 0 (.gTop gid),
      LinearIneq.le (.x a) (dims.width a) (.gRight gid),
      LinearIneq.le (.y a) (dims.height a) (.gBot gid) ]

/-- Translate a binary group constraint (group₂). -/
noncomputable def translate_group₂ (dims : DimCtx) (X : Selector₂) (gids : Atom → GroupId) :
    List LinearIneq :=
  X.toList.flatMap fun (a, b) =>
    let gid := gids a
    [ LinearIneq.geq (.x b) 0 (.gLeft gid),
      LinearIneq.geq (.y b) 0 (.gTop gid),
      LinearIneq.le (.x b) (dims.width b) (.gRight gid),
      LinearIneq.le (.y b) (dims.height b) (.gBot gid) ]

/-- Translate a size constraint: dimensions are baked into DimCtx, no positioning
    constraints emitted. -/
def translate_size (_w _h : ℚ) (_S : Selector₁) : List LinearIneq := []

/-- Translate a hideatom constraint: hidden atoms are removed, no constraints. -/
def translate_hide (_S : Selector₁) : List LinearIneq := []

--------------------------------------------------------------------------------
-- Cyclic translation (disjunctive)
--------------------------------------------------------------------------------

/-- Trig comparison result for deciding which linear inequality to emit. -/
inductive CmpResult | lt | eq | gt
deriving DecidableEq

/-- Oracle providing precomputed trig comparisons. -/
structure TrigOracle where
  cos_cmp : (n i j k : Nat) → CmpResult
  sin_cmp : (n i j k : Nat) → CmpResult

instance : Inhabited Atom := ⟨⟨0⟩⟩

/-- Emit linear inequalities for a single pair (i,j) at offset k. -/
def translate_cyclic_pair (dims : DimCtx) (L : List Atom) (i j k : Nat)
    (oracle : TrigOracle) : List LinearIneq :=
  let n := L.length
  let ai := L[i]!
  let aj := L[j]!
  let h_ineqs := match oracle.cos_cmp n i j k with
    | .eq => [LinearIneq.eq (.x ai) (.x aj)]
    | .lt => [LinearIneq.le (.x ai) (dims.width ai) (.x aj)]
    | .gt => [LinearIneq.le (.x aj) (dims.width aj) (.x ai)]
  let v_ineqs := match oracle.sin_cmp n i j k with
    | .eq => [LinearIneq.eq (.y ai) (.y aj)]
    | .gt => [LinearIneq.le (.y ai) (dims.height ai) (.y aj)]
    | .lt => [LinearIneq.le (.y aj) (dims.height aj) (.y ai)]
  h_ineqs ++ v_ineqs

/-- Emit all pair constraints for a single path L at a single offset k. -/
def translate_cyclic_path_at_k (dims : DimCtx) (L : List Atom) (k : Nat)
    (oracle : TrigOracle) : List LinearIneq :=
  let n := L.length
  let pairs := (List.range n).flatMap fun i =>
    ((List.range n).filter (· > i)).map fun j => (i, j)
  pairs.flatMap fun (i, j) => translate_cyclic_pair dims L i j k oracle

/-- Translate a cyclic constraint as a disjunction over rotation offsets. -/
noncomputable def translate_cyclic (dims : DimCtx) (X : Selector₂) (rot : Rotation)
    (oracle : TrigOracle) : List (List LinearIneq) :=
  let paths := match rot with
    | .clockwise        => maximalSimplePaths X
    | .counterclockwise => (maximalSimplePaths X).map List.reverse
  paths.flatMap fun L =>
    if L.length ≤ 2 then [[]]
    else (List.range L.length).map fun k => translate_cyclic_path_at_k dims L k oracle

/-- Feasibility of a disjunctive system: at least one alternative is feasible. -/
def feasible_disj (alts : List (List LinearIneq)) : Prop :=
  ∃ alt ∈ alts, feasible alt

--------------------------------------------------------------------------------
-- Reconstruction: Assignment → Realization
--------------------------------------------------------------------------------

/-- Reconstruct a `Realization` from a solver assignment. -/
def reconstruct (σ : Assignment) (dims : DimCtx) (atoms : Finset Atom) : Realization :=
  fun a => if a ∈ atoms then
    some ⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩
  else none

lemma reconstruct_some (σ : Assignment) (dims : DimCtx) (atoms : Finset Atom)
    (a : Atom) (ha : a ∈ atoms) :
    reconstruct σ dims atoms a =
      some ⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩ := by
  simp [reconstruct, ha]

lemma reconstruct_none (σ : Assignment) (dims : DimCtx) (atoms : Finset Atom)
    (a : Atom) (ha : a ∉ atoms) :
    reconstruct σ dims atoms a = none := by
  simp [reconstruct, ha]

--------------------------------------------------------------------------------
-- Soundness: Orientation (strict satisfaction → Lean predicate)
--------------------------------------------------------------------------------

theorem orientation_right_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .right, satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .right := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_⟩
  simp only [leftOf]
  have hmem : LinearIneq.le (.x a) (dims.width a) (.x b) ∈
      translate_orientation dims X .right := by
    simp only [translate_orientation]
    exact List.mem_map.mpr ⟨⟨a, b⟩, Finset.mem_toList.mpr hab, rfl⟩
  exact h_sat _ hmem

theorem orientation_left_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .left, satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .left := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_⟩
  simp only [leftOf]
  have hmem : LinearIneq.le (.x b) (dims.width b) (.x a) ∈
      translate_orientation dims X .left := by
    simp only [translate_orientation]
    exact List.mem_map.mpr ⟨⟨a, b⟩, Finset.mem_toList.mpr hab, rfl⟩
  exact h_sat _ hmem

theorem orientation_below_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .below, satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .below := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_⟩
  simp only [above]
  have hmem : LinearIneq.le (.y a) (dims.height a) (.y b) ∈
      translate_orientation dims X .below := by
    simp only [translate_orientation]
    exact List.mem_map.mpr ⟨⟨a, b⟩, Finset.mem_toList.mpr hab, rfl⟩
  exact h_sat _ hmem

theorem orientation_above_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .above, satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .above := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_⟩
  simp only [above]
  have hmem : LinearIneq.le (.y b) (dims.height b) (.y a) ∈
      translate_orientation dims X .above := by
    simp only [translate_orientation]
    exact List.mem_map.mpr ⟨⟨a, b⟩, Finset.mem_toList.mpr hab, rfl⟩
  exact h_sat _ hmem

--------------------------------------------------------------------------------
-- Soundness: Compound Orientation (directly*)
-- Each emits two constraints per pair via flatMap: one ordering + one alignment
--------------------------------------------------------------------------------

/-- Helper: membership in a flatMap-produced list for compound directions. -/
private lemma mem_flatMap_pair {α β : Type*} {f : α → List β} {x : α} {l : List α} {b : β}
    (hx : x ∈ l) (hb : b ∈ f x) : b ∈ l.flatMap f :=
  List.mem_flatMap.mpr ⟨x, hx, hb⟩

theorem orientation_directlyRight_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .directlyRight,
      satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .directlyRight := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_, ?_⟩
  · -- leftOf
    simp only [leftOf]
    have hmem : LinearIneq.le (.x a) (dims.width a) (.x b) ∈
        translate_orientation dims X .directlyRight := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem
  · -- aligned_h
    simp only [aligned_h]
    have hmem : LinearIneq.eq (.y a) (.y b) ∈
        translate_orientation dims X .directlyRight := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem

theorem orientation_directlyLeft_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .directlyLeft,
      satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .directlyLeft := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_, ?_⟩
  · -- leftOf b₂ b₁
    simp only [leftOf]
    have hmem : LinearIneq.le (.x b) (dims.width b) (.x a) ∈
        translate_orientation dims X .directlyLeft := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem
  · -- aligned_h
    simp only [aligned_h]
    have hmem : LinearIneq.eq (.y a) (.y b) ∈
        translate_orientation dims X .directlyLeft := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem

theorem orientation_directlyBelow_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .directlyBelow,
      satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .directlyBelow := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_, ?_⟩
  · -- above b₁ b₂
    simp only [above]
    have hmem : LinearIneq.le (.y a) (dims.height a) (.y b) ∈
        translate_orientation dims X .directlyBelow := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem
  · -- aligned_v
    simp only [aligned_v]
    have hmem : LinearIneq.eq (.x a) (.x b) ∈
        translate_orientation dims X .directlyBelow := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem

theorem orientation_directlyAbove_sound_strict
    (dims : DimCtx) (X : Selector₂) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_orientation dims X .directlyAbove,
      satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ dims atoms) X .directlyAbove := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_, ?_⟩
  · -- above b₂ b₁
    simp only [above]
    have hmem : LinearIneq.le (.y b) (dims.height b) (.y a) ∈
        translate_orientation dims X .directlyAbove := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem
  · -- aligned_v
    simp only [aligned_v]
    have hmem : LinearIneq.eq (.x a) (.x b) ∈
        translate_orientation dims X .directlyAbove := by
      simp only [translate_orientation]
      exact mem_flatMap_pair (Finset.mem_toList.mpr hab) (by simp)
    exact h_sat _ hmem

--------------------------------------------------------------------------------
-- Soundness: Alignment
--------------------------------------------------------------------------------

theorem align_horizontal_sound
    (X : Selector₂) (σ : Assignment) (dims : DimCtx) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_align X .horizontal, satisfies_ineq σ ineq) :
    sat_align (reconstruct σ dims atoms) X .horizontal := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_⟩
  simp only [aligned_h]
  have hmem : LinearIneq.eq (.y a) (.y b) ∈ translate_align X .horizontal := by
    simp only [translate_align]
    exact List.mem_map.mpr ⟨⟨a, b⟩, Finset.mem_toList.mpr hab, rfl⟩
  exact h_sat _ hmem

theorem align_vertical_sound
    (X : Selector₂) (σ : Assignment) (dims : DimCtx) (atoms : Finset Atom)
    (h_atoms : ∀ p ∈ X, p.1 ∈ atoms ∧ p.2 ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_align X .vertical, satisfies_ineq σ ineq) :
    sat_align (reconstruct σ dims atoms) X .vertical := by
  intro a b hab
  have ha := (h_atoms ⟨a, b⟩ hab).1
  have hb := (h_atoms ⟨a, b⟩ hab).2
  refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
          ⟨σ (.x b), σ (.y b), dims.width b, dims.height b⟩,
          reconstruct_some σ dims atoms a ha,
          reconstruct_some σ dims atoms b hb, ?_⟩
  simp only [aligned_v]
  have hmem : LinearIneq.eq (.x a) (.x b) ∈ translate_align X .vertical := by
    simp only [translate_align]
    exact List.mem_map.mpr ⟨⟨a, b⟩, Finset.mem_toList.mpr hab, rfl⟩
  exact h_sat _ hmem

--------------------------------------------------------------------------------
-- Soundness: Group₁
--------------------------------------------------------------------------------

theorem group₁_sound
    (dims : DimCtx) (S : Selector₁) (gid : GroupId) (σ : Assignment) (atoms : Finset Atom)
    (h_atoms_S : ∀ a ∈ S, a ∈ atoms)
    (h_atoms_only : ∀ a ∈ atoms, a ∉ S →
      ¬ (σ (.gLeft gid) ≤ σ (.x a) ∧
         σ (.gTop gid)  ≤ σ (.y a) ∧
         σ (.x a) + dims.width a  ≤ σ (.gRight gid) ∧
         σ (.y a) + dims.height a ≤ σ (.gBot gid)))
    (h_sat : ∀ ineq ∈ translate_group₁ dims S gid, satisfies_ineq σ ineq) :
    sat_group₁_core (reconstruct σ dims atoms) S := by
  refine ⟨⟨σ (.gLeft gid), σ (.gTop gid), σ (.gRight gid), σ (.gBot gid)⟩, ?_⟩
  intro a
  constructor
  · -- Forward: contained in boundary → a ∈ S
    intro ⟨b, hRa, hContains⟩
    by_contra hNotS
    by_cases hmem : a ∈ atoms
    · -- a ∈ atoms, get box info
      have hbox := reconstruct_some σ dims atoms a hmem
      rw [hbox] at hRa
      cases hRa
      simp only [contains] at hContains
      exact h_atoms_only a hmem hNotS hContains
    · -- a ∉ atoms, reconstruct gives none
      have := reconstruct_none σ dims atoms a hmem
      rw [this] at hRa
      exact Option.noConfusion hRa
  · -- Reverse: a ∈ S → contained in boundary
    intro haS
    have ha := h_atoms_S a haS
    refine ⟨⟨σ (.x a), σ (.y a), dims.width a, dims.height a⟩,
            reconstruct_some σ dims atoms a ha, ?_⟩
    simp only [contains]
    -- Extract the four inequality satisfactions for atom a
    have h_in_list : a ∈ S.toList := Finset.mem_toList.mpr haS
    -- geq (.x a) 0 (.gLeft gid) : σ(.x a) ��� σ(.gLeft gid) + 0
    have h1 : satisfies_ineq σ (LinearIneq.geq (.x a) 0 (.gLeft gid)) := by
      apply h_sat
      simp only [translate_group₁]
      exact List.mem_flatMap.mpr ⟨a, h_in_list, by simp⟩
    -- geq (.y a) 0 (.gTop gid) : σ(.y a) ≥ σ(.gTop gid) + 0
    have h2 : satisfies_ineq σ (LinearIneq.geq (.y a) 0 (.gTop gid)) := by
      apply h_sat
      simp only [translate_group₁]
      exact List.mem_flatMap.mpr ⟨a, h_in_list, by simp⟩
    -- le (.x a) (width a) (.gRight gid) : σ(.x a) + width ≤ σ(.gRight gid)
    have h3 : satisfies_ineq σ (LinearIneq.le (.x a) (dims.width a) (.gRight gid)) := by
      apply h_sat
      simp only [translate_group₁]
      exact List.mem_flatMap.mpr ⟨a, h_in_list, by simp⟩
    -- le (.y a) (height a) (.gBot gid) : σ(.y a) + height ≤ σ(.gBot gid)
    have h4 : satisfies_ineq σ (LinearIneq.le (.y a) (dims.height a) (.gBot gid)) := by
      apply h_sat
      simp only [translate_group₁]
      exact List.mem_flatMap.mpr ⟨a, h_in_list, by simp⟩
    simp only [satisfies_ineq] at h1 h2 h3 h4
    exact ⟨by linarith, by linarith, h3, h4⟩

--------------------------------------------------------------------------------
-- Completeness: Assignment extraction from Realization
--------------------------------------------------------------------------------

/-- Extract a solver assignment from a realization. -/
noncomputable def extract_assignment (R : Realization) : Assignment :=
  fun v => match v with
  | .x a     => match R a with | some b => b.x_tl  | none => 0
  | .y a     => match R a with | some b => b.y_tl  | none => 0
  | .gLeft _ => 0
  | .gRight _ => 0
  | .gTop _ => 0
  | .gBot _ => 0

private lemma extract_x (R : Realization) (a : Atom) (b : Box) (h : R a = some b) :
    extract_assignment R (.x a) = b.x_tl := by
  simp [extract_assignment, h]

private lemma extract_y (R : Realization) (a : Atom) (b : Box) (h : R a = some b) :
    extract_assignment R (.y a) = b.y_tl := by
  simp [extract_assignment, h]

--------------------------------------------------------------------------------
-- Completeness: Orientation
--------------------------------------------------------------------------------

theorem orientation_right_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .right) :
    ∀ ineq ∈ translate_orientation dims X .right,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hLeftOf⟩ := h_sat hab'
  simp only [satisfies_ineq, extract_x R a ba hRa, extract_x R b bb hRb]
  have ⟨hw, _⟩ := h_dims a ba hRa
  simp only [leftOf] at hLeftOf
  linarith

theorem orientation_left_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .left) :
    ∀ ineq ∈ translate_orientation dims X .left,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hLeftOf⟩ := h_sat hab'
  simp only [satisfies_ineq, extract_x R a ba hRa, extract_x R b bb hRb]
  have ⟨hw, _⟩ := h_dims b bb hRb
  simp only [leftOf] at hLeftOf
  linarith

theorem orientation_below_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .below) :
    ∀ ineq ∈ translate_orientation dims X .below,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hAbove⟩ := h_sat hab'
  simp only [satisfies_ineq, extract_y R a ba hRa, extract_y R b bb hRb]
  have ⟨_, hh⟩ := h_dims a ba hRa
  simp only [above] at hAbove
  linarith

theorem orientation_above_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .above) :
    ∀ ineq ∈ translate_orientation dims X .above,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hAbove⟩ := h_sat hab'
  simp only [satisfies_ineq, extract_y R a ba hRa, extract_y R b bb hRb]
  have ⟨_, hh⟩ := h_dims b bb hRb
  simp only [above] at hAbove
  linarith

--------------------------------------------------------------------------------
-- Completeness: Compound Orientation (directly*)
-- For flatMap-produced lists, we need to handle two inequalities per pair
--------------------------------------------------------------------------------

theorem orientation_directlyRight_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .directlyRight) :
    ∀ ineq ∈ translate_orientation dims X .directlyRight,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, hineq_mem⟩ := List.mem_flatMap.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hLeftOf, hAligned⟩ := h_sat hab'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq_mem
  rcases hineq_mem with rfl | rfl
  · -- le constraint: leftOf
    simp only [satisfies_ineq, extract_x R a ba hRa, extract_x R b bb hRb]
    have ⟨hw, _⟩ := h_dims a ba hRa
    simp only [leftOf] at hLeftOf; linarith
  · -- eq constraint: aligned_h
    simp only [satisfies_ineq, extract_y R a ba hRa, extract_y R b bb hRb]
    exact hAligned

theorem orientation_directlyLeft_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .directlyLeft) :
    ∀ ineq ∈ translate_orientation dims X .directlyLeft,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, hineq_mem⟩ := List.mem_flatMap.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hLeftOf, hAligned⟩ := h_sat hab'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq_mem
  rcases hineq_mem with rfl | rfl
  · simp only [satisfies_ineq, extract_x R a ba hRa, extract_x R b bb hRb]
    have ⟨hw, _⟩ := h_dims b bb hRb
    simp only [leftOf] at hLeftOf; linarith
  · simp only [satisfies_ineq, extract_y R a ba hRa, extract_y R b bb hRb]
    exact hAligned

theorem orientation_directlyBelow_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .directlyBelow) :
    ∀ ineq ∈ translate_orientation dims X .directlyBelow,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, hineq_mem⟩ := List.mem_flatMap.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hAbove, hAligned⟩ := h_sat hab'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq_mem
  rcases hineq_mem with rfl | rfl
  · simp only [satisfies_ineq, extract_y R a ba hRa, extract_y R b bb hRb]
    have ⟨_, hh⟩ := h_dims a ba hRa
    simp only [above] at hAbove; linarith
  · simp only [satisfies_ineq, extract_x R a ba hRa, extract_x R b bb hRb]
    exact hAligned

theorem orientation_directlyAbove_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X .directlyAbove) :
    ∀ ineq ∈ translate_orientation dims X .directlyAbove,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_orientation] at hineq
  obtain ⟨⟨a, b⟩, hab, hineq_mem⟩ := List.mem_flatMap.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hAbove, hAligned⟩ := h_sat hab'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq_mem
  rcases hineq_mem with rfl | rfl
  · simp only [satisfies_ineq, extract_y R a ba hRa, extract_y R b bb hRb]
    have ⟨_, hh⟩ := h_dims b bb hRb
    simp only [above] at hAbove; linarith
  · simp only [satisfies_ineq, extract_x R a ba hRa, extract_x R b bb hRb]
    exact hAligned

--------------------------------------------------------------------------------
-- Completeness: Alignment
--------------------------------------------------------------------------------

theorem align_horizontal_complete
    (X : Selector₂) (R : Realization) (dims : DimCtx)
    (h_sat : sat_align R X .horizontal) :
    ∀ ineq ∈ translate_align X .horizontal,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_align] at hineq
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hAligned⟩ := h_sat hab'
  simp only [satisfies_ineq, extract_y R a ba hRa, extract_y R b bb hRb]
  exact hAligned

theorem align_vertical_complete
    (X : Selector₂) (R : Realization) (dims : DimCtx)
    (h_sat : sat_align R X .vertical) :
    ∀ ineq ∈ translate_align X .vertical,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_align] at hineq
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hineq
  have hab' := Finset.mem_toList.mp hab
  obtain ⟨ba, bb, hRa, hRb, hAligned⟩ := h_sat hab'
  simp only [satisfies_ineq, extract_x R a ba hRa, extract_x R b bb hRb]
  exact hAligned

--------------------------------------------------------------------------------
-- Completeness: Group₂
--------------------------------------------------------------------------------

/-- Group₂ completeness: if `sat_group₂_core R X` holds and `gids` is injective,
    then a suitable assignment satisfies the emitted bounding-box inequalities.

    Injectivity of `gids` is natural: in the solver, each key atom's group
    gets a distinct GroupId, so the group bounding-box variables are independent. -/
theorem group₂_complete
    (dims : DimCtx) (X : Selector₂) (R : Realization) (gids : Atom → GroupId)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_inj : Function.Injective gids)
    (h_sat : sat_group₂_core R X) :
    ∃ σ, ∀ ineq ∈ translate_group₂ dims X gids, satisfies_ineq σ ineq := by
  classical
  obtain ⟨fam, hfam⟩ := h_sat
  -- Build assignment: atom coords from R, group vars from fam via gids⁻¹
  let σ : Assignment := fun v => match v with
    | .x a      => match R a with | some b => b.x_tl  | none => 0
    | .y a      => match R a with | some b => b.y_tl  | none => 0
    | .gLeft g  => if h : ∃ a, gids a = g then (fam h.choose).x_tl else 0
    | .gTop g   => if h : ∃ a, gids a = g then (fam h.choose).y_tl else 0
    | .gRight g => if h : ∃ a, gids a = g then (fam h.choose).x_br else 0
    | .gBot g   => if h : ∃ a, gids a = g then (fam h.choose).y_br else 0
  refine ⟨σ, fun ineq hineq => ?_⟩
  simp only [translate_group₂] at hineq
  obtain ⟨⟨a, b⟩, hab, hineq_mem⟩ := List.mem_flatMap.mp hineq
  have hab' := Finset.mem_toList.mp hab
  have ha_first : a ∈ firstOf X := by
    simp only [firstOf, Finset.mem_image]
    exact ⟨⟨a, b⟩, hab', rfl⟩
  have hcontains := (hfam a ha_first b).mpr hab'
  obtain ⟨bb, hRb, hcont⟩ := hcontains
  simp only [contains] at hcont
  obtain ⟨hx_left, hy_top, hx_right, hy_bot⟩ := hcont
  have ⟨hw, hh⟩ := h_dims b bb hRb
  have hg_exists : ∃ a', gids a' = gids a := ⟨a, rfl⟩
  have hg_choose : Exists.choose hg_exists = a :=
    h_inj (Exists.choose_spec hg_exists)
  -- Helper: the σ values for group variables at gids a
  have σ_gLeft : σ (.gLeft (gids a)) = (fam a).x_tl := by
    show (if h : ∃ a', gids a' = gids a then (fam h.choose).x_tl else 0) = _
    rw [dif_pos hg_exists, hg_choose]
  have σ_gTop : σ (.gTop (gids a)) = (fam a).y_tl := by
    show (if h : ∃ a', gids a' = gids a then (fam h.choose).y_tl else 0) = _
    rw [dif_pos hg_exists, hg_choose]
  have σ_gRight : σ (.gRight (gids a)) = (fam a).x_br := by
    show (if h : ∃ a', gids a' = gids a then (fam h.choose).x_br else 0) = _
    rw [dif_pos hg_exists, hg_choose]
  have σ_gBot : σ (.gBot (gids a)) = (fam a).y_br := by
    show (if h : ∃ a', gids a' = gids a then (fam h.choose).y_br else 0) = _
    rw [dif_pos hg_exists, hg_choose]
  have σ_xb : σ (.x b) = bb.x_tl := by show (match R b with | some b => b.x_tl | none => 0) = _; rw [hRb]
  have σ_yb : σ (.y b) = bb.y_tl := by show (match R b with | some b => b.y_tl | none => 0) = _; rw [hRb]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq_mem
  rcases hineq_mem with rfl | rfl | rfl | rfl
  · simp only [satisfies_ineq]; rw [σ_xb, σ_gLeft]; linarith
  · simp only [satisfies_ineq]; rw [σ_yb, σ_gTop]; linarith
  · simp only [satisfies_ineq]; rw [σ_xb, σ_gRight]; linarith
  · simp only [satisfies_ineq]; rw [σ_yb, σ_gBot]; linarith

--------------------------------------------------------------------------------
-- Cyclic Soundness/Completeness
--------------------------------------------------------------------------------

/-- A trig oracle is correct if its comparisons match the actual trig functions
    used in Main.lean's `hrel`/`vrel` definitions. -/
def TrigOracle.correct (oracle : TrigOracle) : Prop :=
  ∀ n i j k : Nat,
    (oracle.cos_cmp n i j k = .lt ↔
      Real.cos ((i + k) * angleStep n) < Real.cos ((j + k) * angleStep n)) ∧
    (oracle.cos_cmp n i j k = .eq ↔
      Real.cos ((i + k) * angleStep n) = Real.cos ((j + k) * angleStep n)) ∧
    (oracle.cos_cmp n i j k = .gt ↔
      Real.cos ((i + k) * angleStep n) > Real.cos ((j + k) * angleStep n)) ∧
    (oracle.sin_cmp n i j k = .lt ↔
      Real.sin ((i + k) * angleStep n) < Real.sin ((j + k) * angleStep n)) ∧
    (oracle.sin_cmp n i j k = .eq ↔
      Real.sin ((i + k) * angleStep n) = Real.sin ((j + k) * angleStep n)) ∧
    (oracle.sin_cmp n i j k = .gt ↔
      Real.sin ((i + k) * angleStep n) > Real.sin ((j + k) * angleStep n))

/-- nth! and getElem! agree for valid indices. -/
private lemma nth!_eq_getElem_bang (L : List Atom) (i : Nat) (h : i < L.length) :
    nth! L i h = L[i]! := by
  unfold nth!
  induction L generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n (Nat.lt_of_succ_lt_succ h)

/-- An index pair (i,j) with i < j < n is in the pair list used by translate_cyclic_path_at_k. -/
private lemma pair_mem_pairs (n i j : Nat) (hij : i < j) (hjn : j < n) :
    (i, j) ∈ (List.range n).flatMap fun i' =>
      ((List.range n).filter (· > i')).map fun j' => (i', j') := by
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr (Nat.lt_trans hij hjn), ?_⟩
  apply List.mem_map.mpr
  refine ⟨j, ?_, rfl⟩
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  omega

/-- Membership: ineqs from translate_cyclic_pair at valid pair (i,j) are
    in translate_cyclic_path_at_k. -/
private lemma ineq_mem_path_at_k (dims : DimCtx) (L : List Atom) (k i j : Nat)
    (oracle : TrigOracle) (hij : i < j) (hjn : j < L.length) (ineq : LinearIneq)
    (hineq : ineq ∈ translate_cyclic_pair dims L i j k oracle) :
    ineq ∈ translate_cyclic_path_at_k dims L k oracle := by
  simp only [translate_cyclic_path_at_k]
  apply List.mem_flatMap.mpr
  exact ⟨(i, j), pair_mem_pairs L.length i j hij hjn, hineq⟩

/-- Per-pair hrel soundness: strict satisfaction of the cos-dispatched inequalities
    gives the horizontal relation. -/
private theorem cyclic_pair_hrel_sound
    (dims : DimCtx) (L : List Atom) (i j k : Nat) (σ : Assignment) (atoms : Finset Atom)
    (oracle : TrigOracle) (h_oracle : oracle.correct)
    (hi : i < L.length) (hj : j < L.length)
    (h_ai : nth! L i hi ∈ atoms) (h_aj : nth! L j hj ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_cyclic_pair dims L i j k oracle,
      satisfies_ineq_strict σ ineq) :
    hrel (reconstruct σ dims atoms) L i j k hi hj := by
  set ai := nth! L i hi
  set aj := nth! L j hj
  have hai : ai = L[i]! := nth!_eq_getElem_bang L i hi
  have haj : aj = L[j]! := nth!_eq_getElem_bang L j hj
  refine ⟨⟨σ (.x ai), σ (.y ai), dims.width ai, dims.height ai⟩,
          ⟨σ (.x aj), σ (.y aj), dims.width aj, dims.height aj⟩,
          reconstruct_some σ dims atoms ai h_ai,
          reconstruct_some σ dims atoms aj h_aj, ?_⟩
  obtain ⟨hcos_lt, hcos_eq, hcos_gt, _, _, _⟩ := h_oracle L.length i j k
  -- Unfold let bindings, then dispatch on oracle result
  dsimp only
  rcases h_cos : oracle.cos_cmp L.length i j k with _ | _ | _
  · -- .lt: cos θi < cos θj → leftOf bi bj
    have hlt := hcos_lt.mp h_cos
    rw [if_neg (ne_of_lt hlt), if_pos hlt]; simp only [leftOf]
    have hmem : LinearIneq.le (.x L[i]!) (dims.width L[i]!) (.x L[j]!) ∈
        translate_cyclic_pair dims L i j k oracle := by
      simp [translate_cyclic_pair, h_cos]
    have h_ineq := h_sat _ hmem
    simp only [satisfies_ineq_strict] at h_ineq
    rw [hai, haj]; exact h_ineq
  · -- .eq: cos θi = cos θj → aligned_v bi bj
    rw [if_pos (hcos_eq.mp h_cos)]; simp only [aligned_v]
    have hmem : LinearIneq.eq (.x L[i]!) (.x L[j]!) ∈
        translate_cyclic_pair dims L i j k oracle := by
      simp [translate_cyclic_pair, h_cos]
    have h_ineq := h_sat _ hmem
    simp only [satisfies_ineq_strict] at h_ineq
    rw [hai, haj]; exact h_ineq
  · -- .gt: cos θi > cos θj → leftOf bj bi
    have hgt := hcos_gt.mp h_cos
    rw [if_neg (ne_of_gt hgt), if_neg (not_lt_of_gt hgt)]; simp only [leftOf]
    have hmem : LinearIneq.le (.x L[j]!) (dims.width L[j]!) (.x L[i]!) ∈
        translate_cyclic_pair dims L i j k oracle := by
      simp [translate_cyclic_pair, h_cos]
    have h_ineq := h_sat _ hmem
    simp only [satisfies_ineq_strict] at h_ineq
    rw [hai, haj]; exact h_ineq

/-- Per-pair vrel soundness: strict satisfaction of the sin-dispatched inequalities
    gives the vertical relation. -/
private theorem cyclic_pair_vrel_sound
    (dims : DimCtx) (L : List Atom) (i j k : Nat) (σ : Assignment) (atoms : Finset Atom)
    (oracle : TrigOracle) (h_oracle : oracle.correct)
    (hi : i < L.length) (hj : j < L.length)
    (h_ai : nth! L i hi ∈ atoms) (h_aj : nth! L j hj ∈ atoms)
    (h_sat : ∀ ineq ∈ translate_cyclic_pair dims L i j k oracle,
      satisfies_ineq_strict σ ineq) :
    vrel (reconstruct σ dims atoms) L i j k hi hj := by
  set ai := nth! L i hi
  set aj := nth! L j hj
  have hai : ai = L[i]! := nth!_eq_getElem_bang L i hi
  have haj : aj = L[j]! := nth!_eq_getElem_bang L j hj
  refine ⟨⟨σ (.x ai), σ (.y ai), dims.width ai, dims.height ai⟩,
          ⟨σ (.x aj), σ (.y aj), dims.width aj, dims.height aj⟩,
          reconstruct_some σ dims atoms ai h_ai,
          reconstruct_some σ dims atoms aj h_aj, ?_⟩
  obtain ⟨_, _, _, hsin_lt, hsin_eq, hsin_gt⟩ := h_oracle L.length i j k
  dsimp only
  rcases h_sin : oracle.sin_cmp L.length i j k with _ | _ | _
  · -- .lt: sin θi < sin θj → above bj bi
    have hlt := hsin_lt.mp h_sin
    rw [if_neg (ne_of_lt hlt), if_neg (not_lt.mpr (le_of_lt hlt))]; simp only [above]
    have hmem : LinearIneq.le (.y L[j]!) (dims.height L[j]!) (.y L[i]!) ∈
        translate_cyclic_pair dims L i j k oracle := by
      simp [translate_cyclic_pair, h_sin]
    have h_ineq := h_sat _ hmem
    simp only [satisfies_ineq_strict] at h_ineq
    rw [hai, haj]; exact h_ineq
  · -- .eq: sin θi = sin θj → aligned_h bi bj
    rw [if_pos (hsin_eq.mp h_sin)]; simp only [aligned_h]
    have hmem : LinearIneq.eq (.y L[i]!) (.y L[j]!) ∈
        translate_cyclic_pair dims L i j k oracle := by
      simp [translate_cyclic_pair, h_sin]
    have h_ineq := h_sat _ hmem
    simp only [satisfies_ineq_strict] at h_ineq
    rw [hai, haj]; exact h_ineq
  · -- .gt: sin θi > sin θj → above bi bj
    have hgt := hsin_gt.mp h_sin
    rw [if_neg (ne_of_gt hgt), if_pos hgt]; simp only [above]
    have hmem : LinearIneq.le (.y L[i]!) (dims.height L[i]!) (.y L[j]!) ∈
        translate_cyclic_pair dims L i j k oracle := by
      simp [translate_cyclic_pair, h_sin]
    have h_ineq := h_sat _ hmem
    simp only [satisfies_ineq_strict] at h_ineq
    rw [hai, haj]; exact h_ineq

/-- Per-path soundness: strict satisfaction of translate_cyclic_path_at_k
    gives allPairs_ok. -/
private theorem cyclic_path_sound
    (dims : DimCtx) (L : List Atom) (k : Nat) (σ : Assignment) (atoms : Finset Atom)
    (oracle : TrigOracle) (h_oracle : oracle.correct)
    (h_atoms : ∀ a ∈ L, a ∈ atoms)
    (hk : k < L.length) (hn : 2 < L.length)
    (h_sat : ∀ ineq ∈ translate_cyclic_path_at_k dims L k oracle,
      satisfies_ineq_strict σ ineq) :
    allPairs_ok (reconstruct σ dims atoms) L k := by
  refine ⟨by omega, fun i j hij hjn => ?_⟩
  have hi : i < L.length := Nat.lt_trans hij hjn
  -- Atoms at valid indices are in atoms
  have h_ai : nth! L i hi ∈ atoms :=
    h_atoms (nth! L i hi) (by unfold nth!; exact List.get_mem L ⟨i, hi⟩)
  have h_aj : nth! L j hjn ∈ atoms :=
    h_atoms (nth! L j hjn) (by unfold nth!; exact List.get_mem L ⟨j, hjn⟩)
  -- Satisfaction of per-pair ineqs follows from per-path satisfaction
  have h_pair_sat : ∀ ineq ∈ translate_cyclic_pair dims L i j k oracle,
      satisfies_ineq_strict σ ineq := by
    intro ineq hineq
    exact h_sat _ (ineq_mem_path_at_k dims L k i j oracle hij hjn ineq hineq)
  exact ⟨cyclic_pair_hrel_sound dims L i j k σ atoms oracle h_oracle hi hjn h_ai h_aj h_pair_sat,
         cyclic_pair_vrel_sound dims L i j k σ atoms oracle h_oracle hi hjn h_ai h_aj h_pair_sat⟩

/-- Cyclic soundness: if for each path of length > 2, there is a rotation offset k
    whose linear system is strictly satisfied, then sat_cyclic holds.

    The per-path hypothesis mirrors the solver's backtracking: for each path,
    the solver picks one offset k and solves the conjunctive system at that k. -/
theorem cyclic_sound
    (dims : DimCtx) (X : Selector₂) (rot : Rotation)
    (oracle : TrigOracle) (σ : Assignment) (atoms : Finset Atom)
    (h_oracle : oracle.correct)
    (h_atoms_paths : ∀ L ∈ maximalSimplePaths X, ∀ a ∈ L, a ∈ atoms)
    (h_feasible : ∀ L ∈ (match rot with
        | .clockwise => maximalSimplePaths X
        | .counterclockwise => (maximalSimplePaths X).map List.reverse),
      2 < L.length →
      ∃ k, k < L.length ∧ ∀ ineq ∈ translate_cyclic_path_at_k dims L k oracle,
        satisfies_ineq_strict σ ineq) :
    sat_cyclic (reconstruct σ dims atoms) X rot := by
  cases rot with
  | clockwise =>
    intro L hL hn
    obtain ⟨k, hk, h_sat_k⟩ := h_feasible L (by exact hL) hn
    exact ⟨k, hk, cyclic_path_sound dims L k σ atoms oracle h_oracle
      (h_atoms_paths L hL) hk hn h_sat_k⟩
  | counterclockwise =>
    -- sat_cyclic_ccw: ∀ L ∈ maximalSimplePaths X, let L' := L.reverse; 2 < L'.length → ∃ k, ...
    intro L hL
    -- After intro, goal has `let L' := L.reverse; ...`; unfold the let
    show 2 < L.reverse.length → ∃ k, k < L.reverse.length ∧ allPairs_ok (reconstruct σ dims atoms) L.reverse k
    intro hn
    -- L ∈ maximalSimplePaths X; work with L.reverse
    have hLrev_mem : L.reverse ∈ (maximalSimplePaths X).map List.reverse :=
      List.mem_map.mpr ⟨L, hL, rfl⟩
    obtain ⟨k, hk, h_sat_k⟩ := h_feasible L.reverse hLrev_mem hn
    have h_atoms_rev : ∀ a ∈ L.reverse, a ∈ atoms :=
      fun a ha => h_atoms_paths L hL a (List.mem_reverse.mp ha)
    exact ⟨k, hk, cyclic_path_sound dims L.reverse k σ atoms oracle h_oracle
      h_atoms_rev hk hn h_sat_k⟩

/-- Per-pair hrel completeness: if hrel holds, the extracted assignment satisfies
    the cos-dispatched inequalities (non-strict). -/
private theorem cyclic_pair_hrel_complete
    (dims : DimCtx) (L : List Atom) (i j k : Nat) (R : Realization)
    (oracle : TrigOracle) (h_oracle : oracle.correct)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (hi : i < L.length) (hj : j < L.length)
    (h_hrel : hrel R L i j k hi hj)
    (ineq : LinearIneq)
    (hineq : ineq ∈ (match oracle.cos_cmp L.length i j k with
      | .eq => [LinearIneq.eq (.x L[i]!) (.x L[j]!)]
      | .lt => [LinearIneq.le (.x L[i]!) (dims.width L[i]!) (.x L[j]!)]
      | .gt => [LinearIneq.le (.x L[j]!) (dims.width L[j]!) (.x L[i]!)])) :
    satisfies_ineq (extract_assignment R) ineq := by
  obtain ⟨bi, bj, hRi, hRj, h_cond⟩ := h_hrel
  dsimp only at h_cond
  have hai : L[i]! = nth! L i hi := (nth!_eq_getElem_bang L i hi).symm
  have haj : L[j]! = nth! L j hj := (nth!_eq_getElem_bang L j hj).symm
  have hRi' : R L[i]! = some bi := by rw [hai]; exact hRi
  have hRj' : R L[j]! = some bj := by rw [haj]; exact hRj
  obtain ⟨hwi, _⟩ := h_dims L[i]! bi hRi'
  obtain ⟨hwj, _⟩ := h_dims L[j]! bj hRj'
  obtain ⟨hcos_lt, hcos_eq, hcos_gt, _, _, _⟩ := h_oracle L.length i j k
  rcases h_cos : oracle.cos_cmp L.length i j k with _ | _ | _
  · -- .lt → leftOf bi bj
    rw [h_cos] at hineq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq; subst hineq
    have hlt := hcos_lt.mp h_cos
    rw [if_neg (ne_of_lt hlt), if_pos hlt] at h_cond
    simp only [satisfies_ineq, extract_x R L[i]! bi hRi', extract_x R L[j]! bj hRj']
    simp only [leftOf] at h_cond; rw [← hwi]; linarith
  · -- .eq → aligned_v bi bj
    rw [h_cos] at hineq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq; subst hineq
    rw [if_pos (hcos_eq.mp h_cos)] at h_cond
    simp only [satisfies_ineq, extract_x R L[i]! bi hRi', extract_x R L[j]! bj hRj']
    simp only [aligned_v] at h_cond; exact h_cond
  · -- .gt → leftOf bj bi
    rw [h_cos] at hineq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq; subst hineq
    have hgt := hcos_gt.mp h_cos
    rw [if_neg (ne_of_gt hgt), if_neg (not_lt_of_gt hgt)] at h_cond
    simp only [satisfies_ineq, extract_x R L[j]! bj hRj', extract_x R L[i]! bi hRi']
    simp only [leftOf] at h_cond; rw [← hwj]; linarith

/-- Per-pair vrel completeness: if vrel holds, the extracted assignment satisfies
    the sin-dispatched inequalities (non-strict). -/
private theorem cyclic_pair_vrel_complete
    (dims : DimCtx) (L : List Atom) (i j k : Nat) (R : Realization)
    (oracle : TrigOracle) (h_oracle : oracle.correct)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (hi : i < L.length) (hj : j < L.length)
    (h_vrel : vrel R L i j k hi hj)
    (ineq : LinearIneq)
    (hineq : ineq ∈ (match oracle.sin_cmp L.length i j k with
      | .eq => [LinearIneq.eq (.y L[i]!) (.y L[j]!)]
      | .gt => [LinearIneq.le (.y L[i]!) (dims.height L[i]!) (.y L[j]!)]
      | .lt => [LinearIneq.le (.y L[j]!) (dims.height L[j]!) (.y L[i]!)])) :
    satisfies_ineq (extract_assignment R) ineq := by
  obtain ⟨bi, bj, hRi, hRj, h_cond⟩ := h_vrel
  dsimp only at h_cond
  have hai : L[i]! = nth! L i hi := (nth!_eq_getElem_bang L i hi).symm
  have haj : L[j]! = nth! L j hj := (nth!_eq_getElem_bang L j hj).symm
  have hRi' : R L[i]! = some bi := by rw [hai]; exact hRi
  have hRj' : R L[j]! = some bj := by rw [haj]; exact hRj
  obtain ⟨_, hhi⟩ := h_dims L[i]! bi hRi'
  obtain ⟨_, hhj⟩ := h_dims L[j]! bj hRj'
  obtain ⟨_, _, _, hsin_lt, hsin_eq, hsin_gt⟩ := h_oracle L.length i j k
  rcases h_sin : oracle.sin_cmp L.length i j k with _ | _ | _
  · -- .lt → above bj bi
    rw [h_sin] at hineq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq; subst hineq
    have hlt := hsin_lt.mp h_sin
    rw [if_neg (ne_of_lt hlt), if_neg (not_lt.mpr (le_of_lt hlt))] at h_cond
    simp only [satisfies_ineq, extract_y R L[j]! bj hRj', extract_y R L[i]! bi hRi']
    simp only [above] at h_cond; rw [← hhj]; linarith
  · -- .eq → aligned_h bi bj
    rw [h_sin] at hineq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq; subst hineq
    rw [if_pos (hsin_eq.mp h_sin)] at h_cond
    simp only [satisfies_ineq, extract_y R L[i]! bi hRi', extract_y R L[j]! bj hRj']
    simp only [aligned_h] at h_cond; exact h_cond
  · -- .gt → above bi bj
    rw [h_sin] at hineq; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hineq; subst hineq
    have hgt := hsin_gt.mp h_sin
    rw [if_neg (ne_of_gt hgt), if_pos hgt] at h_cond
    simp only [satisfies_ineq, extract_y R L[i]! bi hRi', extract_y R L[j]! bj hRj']
    simp only [above] at h_cond; rw [← hhi]; linarith

/-- Per-path completeness: if allPairs_ok holds at offset k, the extracted
    assignment satisfies translate_cyclic_path_at_k. -/
private theorem cyclic_path_complete
    (dims : DimCtx) (L : List Atom) (k : Nat) (R : Realization)
    (oracle : TrigOracle) (h_oracle : oracle.correct)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (hk : k < L.length) (hn : 2 < L.length)
    (h_ok : allPairs_ok R L k) :
    ∀ ineq ∈ translate_cyclic_path_at_k dims L k oracle,
      satisfies_ineq (extract_assignment R) ineq := by
  intro ineq hineq
  simp only [translate_cyclic_path_at_k] at hineq
  obtain ⟨⟨i, j⟩, h_pair, h_ineq_mem⟩ := List.mem_flatMap.mp hineq
  -- Extract i < j < n from pair membership
  have h_pair_mem := List.mem_flatMap.mp h_pair
  obtain ⟨i', hi'_range, h_ij_mem⟩ := h_pair_mem
  obtain ⟨j', hj'_mem, hpair_eq⟩ := List.mem_map.mp h_ij_mem
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj'_mem
  have hij_eq : (i, j) = (i', j') := hpair_eq.symm
  have hi_eq : i = i' := Prod.mk.inj hij_eq |>.1
  have hj_eq : j = j' := Prod.mk.inj hij_eq |>.2
  subst hi_eq; subst hj_eq
  have hjn : j < L.length := hj'_mem.1
  have hij : i < j := hj'_mem.2
  have hi : i < L.length := Nat.lt_trans hij hjn
  -- Get allPairs_ok for this pair
  have ⟨h_hrel, h_vrel⟩ := h_ok.2 i j hij hjn
  -- The ineq is in translate_cyclic_pair = h_ineqs ++ v_ineqs
  simp only [translate_cyclic_pair] at h_ineq_mem
  rcases List.mem_append.mp h_ineq_mem with h_in_h | h_in_v
  · -- In h_ineqs (cos-dispatched)
    exact cyclic_pair_hrel_complete dims L i j k R oracle h_oracle h_dims hi hjn h_hrel ineq h_in_h
  · -- In v_ineqs (sin-dispatched)
    exact cyclic_pair_vrel_complete dims L i j k R oracle h_oracle h_dims hi hjn h_vrel ineq h_in_v

/-- Cyclic completeness: if sat_cyclic holds and the oracle is correct,
    for each path there exists a feasible offset in the disjunctive system.

    Specifically, for each path L, the offset k witnessing allPairs_ok
    yields a satisfied alternative in translate_cyclic. -/
theorem cyclic_complete
    (dims : DimCtx) (X : Selector₂) (rot : Rotation)
    (oracle : TrigOracle) (R : Realization)
    (h_oracle : oracle.correct)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_cyclic R X rot) :
    ∀ L ∈ (match rot with
        | .clockwise => maximalSimplePaths X
        | .counterclockwise => (maximalSimplePaths X).map List.reverse),
      2 < L.length →
      ∃ k, k < L.length ∧ ∀ ineq ∈ translate_cyclic_path_at_k dims L k oracle,
        satisfies_ineq (extract_assignment R) ineq := by
  cases rot with
  | clockwise =>
    intro L hL hn
    obtain ⟨k, hk, h_ok⟩ := h_sat L hL hn
    exact ⟨k, hk, cyclic_path_complete dims L k R oracle h_oracle h_dims hk hn h_ok⟩
  | counterclockwise =>
    -- Goal: ∀ L ∈ (maximalSimplePaths X).map List.reverse, 2 < L.length → ...
    -- h_sat : sat_cyclic_ccw = ∀ L ∈ maximalSimplePaths X, let L' := L.reverse; 2 < L'.length → ...
    intro Lrev hLrev hn
    -- Lrev ∈ (maximalSimplePaths X).map List.reverse, so Lrev = L.reverse for some L ∈ maximalSimplePaths X
    obtain ⟨L, hL, hLrev_eq⟩ := List.mem_map.mp hLrev
    subst hLrev_eq
    -- h_sat L hL : let L' := L.reverse; 2 < L'.length → ∃ k, ...
    -- which is: 2 < L.reverse.length → ∃ k, k < L.reverse.length ∧ allPairs_ok R L.reverse k
    obtain ⟨k, hk, h_ok⟩ := h_sat L hL hn
    exact ⟨k, hk, cyclic_path_complete dims L.reverse k R oracle h_oracle h_dims hk hn h_ok⟩

--------------------------------------------------------------------------------
-- UNSAT Soundness (all orientation directions)
--------------------------------------------------------------------------------

/-- UNSAT soundness for all 8 orientation directions: if a realization satisfies
    the Lean predicate, then the extracted assignment satisfies the emitted system.
    Contrapositive: emitted system infeasible → Lean denotation empty. -/
theorem unsat_soundness_orientation (dims : DimCtx) (X : Selector₂) (d : Direction)
    (R : Realization)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (h_sat : sat_orientation R X d) :
    ∃ σ, ∀ ineq ∈ translate_orientation dims X d, satisfies_ineq σ ineq := by
  cases d with
  | right => exact ⟨_, orientation_right_complete dims X R h_dims h_sat⟩
  | left => exact ⟨_, orientation_left_complete dims X R h_dims h_sat⟩
  | below => exact ⟨_, orientation_below_complete dims X R h_dims h_sat⟩
  | above => exact ⟨_, orientation_above_complete dims X R h_dims h_sat⟩
  | directlyRight => exact ⟨_, orientation_directlyRight_complete dims X R h_dims h_sat⟩
  | directlyLeft => exact ⟨_, orientation_directlyLeft_complete dims X R h_dims h_sat⟩
  | directlyBelow => exact ⟨_, orientation_directlyBelow_complete dims X R h_dims h_sat⟩
  | directlyAbove => exact ⟨_, orientation_directlyAbove_complete dims X R h_dims h_sat⟩

--------------------------------------------------------------------------------
-- Top-Level Theorems
--------------------------------------------------------------------------------

/-- Context for the top-level solver bridge: the atoms, dimensions, and
    group ID assignment that the solver operates over. -/
structure SolverCtx where
  atoms : Finset Atom
  dims  : DimCtx
  gids  : Atom → GroupId
  oracle : TrigOracle

/-- A conjunctive translation of a single positive constraint.
    Cyclic constraints produce disjunctions (handled separately). -/
noncomputable def translate_constraint_conj (ctx : SolverCtx) :
    Constraint → List LinearIneq
  | .orientation X d => translate_orientation ctx.dims X d
  | .align X a       => translate_align X a
  | .group₁ S        => translate_group₁ ctx.dims S ⟨0⟩  -- default group ID
  | .group₂ X _      => translate_group₂ ctx.dims X ctx.gids
  | .size w h S       => translate_size w h S
  | .hideatom S       => translate_hide S
  | .cyclic _ _       => []   -- cyclic handled via disjunctive system

/-- Translate an entire program's conjunctive constraints. -/
noncomputable def translate_program_conj (ctx : SolverCtx) (P : Program) :
    List LinearIneq :=
  P.toList.flatMap fun qc =>
    match qc.holds with
    | .always => translate_constraint_conj ctx qc.constraint
    | .never  => []   -- negated constraints handled separately by the solver

/-- Membership: translated inequalities for a constraint in P are in the program
    translation. This is the key sublist/containment lemma for composing
    per-constraint results into program-level theorems. -/
lemma translate_constraint_mem_program (ctx : SolverCtx) (P : Program)
    (qc : QualifiedConstraint) (hmem : qc ∈ P) (hmode : qc.holds = .always)
    (ineq : LinearIneq) (hineq : ineq ∈ translate_constraint_conj ctx qc.constraint) :
    ineq ∈ translate_program_conj ctx P := by
  simp only [translate_program_conj]
  exact List.mem_flatMap.mpr ⟨qc, Finset.mem_toList.mpr hmem, by rw [hmode]; exact hineq⟩

/-- **Solver soundness for orientation.**
    If the full program's linear system is strictly satisfied,
    any orientation constraint in the program holds on the reconstructed realization. -/
theorem solver_sound_orientation (ctx : SolverCtx) (P : Program) (σ : Assignment)
    (X : Selector₂) (d : Direction)
    (h_atoms : ∀ p ∈ X, p.1 ∈ ctx.atoms ∧ p.2 ∈ ctx.atoms)
    (hmem : ⟨.orientation X d, .always⟩ ∈ P)
    (h_sat : ∀ ineq ∈ translate_program_conj ctx P, satisfies_ineq_strict σ ineq) :
    sat_orientation (reconstruct σ ctx.dims ctx.atoms) X d := by
  cases d with
  | right =>
    apply orientation_right_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))
  | left =>
    apply orientation_left_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))
  | below =>
    apply orientation_below_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))
  | above =>
    apply orientation_above_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))
  | directlyRight =>
    apply orientation_directlyRight_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))
  | directlyLeft =>
    apply orientation_directlyLeft_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))
  | directlyBelow =>
    apply orientation_directlyBelow_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))
  | directlyAbove =>
    apply orientation_directlyAbove_sound_strict ctx.dims X σ ctx.atoms h_atoms
    intro ineq hineq
    exact h_sat _ (translate_constraint_mem_program ctx P _ hmem rfl ineq
      (by simp only [translate_constraint_conj]; exact hineq))

/-- **Solver soundness for alignment.**
    If the full program's linear system is strictly satisfied,
    any alignment constraint in the program holds on the reconstructed realization. -/
theorem solver_sound_align (ctx : SolverCtx) (P : Program) (σ : Assignment)
    (X : Selector₂) (a : AlignDir)
    (h_atoms : ∀ p ∈ X, p.1 ∈ ctx.atoms ∧ p.2 ∈ ctx.atoms)
    (hmem : ⟨.align X a, .always⟩ ∈ P)
    (h_sat : ∀ ineq ∈ translate_program_conj ctx P, satisfies_ineq_strict σ ineq) :
    sat_align (reconstruct σ ctx.dims ctx.atoms) X a := by
  cases a with
  | horizontal =>
    apply align_horizontal_sound X σ ctx.dims ctx.atoms h_atoms
    intro ineq hineq
    exact strict_implies_nonstrict σ ineq (h_sat _
      (translate_constraint_mem_program ctx P _ hmem rfl ineq
        (by simp only [translate_constraint_conj]; exact hineq)))
  | vertical =>
    apply align_vertical_sound X σ ctx.dims ctx.atoms h_atoms
    intro ineq hineq
    exact strict_implies_nonstrict σ ineq (h_sat _
      (translate_constraint_mem_program ctx P _ hmem rfl ineq
        (by simp only [translate_constraint_conj]; exact hineq)))

/-- **Solver completeness for orientation.**
    If a realization is in ⟦P⟧ and P contains an orientation constraint with
    `holds: always`, the extracted assignment satisfies the emitted system. -/
theorem solver_complete_orientation (dims : DimCtx) (X : Selector₂) (d : Direction)
    (P : Program) (R : Realization)
    (h_R : R ∈ denotes P)
    (h_dims : ∀ a b, R a = some b → b.width = dims.width a ∧ b.height = dims.height a)
    (hmem : ⟨.orientation X d, .always⟩ ∈ P) :
    ∀ ineq ∈ translate_orientation dims X d,
      satisfies_ineq (extract_assignment R) ineq := by
  have hsat := h_R.2 _ hmem
  simp only [modelsQC, modelsC] at hsat
  cases d with
  | right => exact orientation_right_complete dims X R h_dims hsat
  | left => exact orientation_left_complete dims X R h_dims hsat
  | below => exact orientation_below_complete dims X R h_dims hsat
  | above => exact orientation_above_complete dims X R h_dims hsat
  | directlyRight => exact orientation_directlyRight_complete dims X R h_dims hsat
  | directlyLeft => exact orientation_directlyLeft_complete dims X R h_dims hsat
  | directlyBelow => exact orientation_directlyBelow_complete dims X R h_dims hsat
  | directlyAbove => exact orientation_directlyAbove_complete dims X R h_dims hsat

/-- **Solver completeness for alignment.**
    If a realization is in ⟦P⟧ and P contains an alignment constraint with
    `holds: always`, the extracted assignment satisfies the emitted system. -/
theorem solver_complete_align (X : Selector₂) (a : AlignDir) (dims : DimCtx)
    (P : Program) (R : Realization)
    (h_R : R ∈ denotes P)
    (hmem : ⟨.align X a, .always⟩ ∈ P) :
    ∀ ineq ∈ translate_align X a,
      satisfies_ineq (extract_assignment R) ineq := by
  have hsat := h_R.2 _ hmem
  simp only [modelsQC, modelsC] at hsat
  cases a with
  | horizontal => exact align_horizontal_complete X R dims hsat
  | vertical => exact align_vertical_complete X R dims hsat

--------------------------------------------------------------------------------
-- Summary
--------------------------------------------------------------------------------

-- Soundness (strict): emitted system satisfied strictly → Lean predicate holds
section Soundness
#check orientation_right_sound_strict
#check orientation_left_sound_strict
#check orientation_below_sound_strict
#check orientation_above_sound_strict
#check orientation_directlyRight_sound_strict
#check orientation_directlyLeft_sound_strict
#check orientation_directlyBelow_sound_strict
#check orientation_directlyAbove_sound_strict
#check align_horizontal_sound
#check align_vertical_sound
#check group₁_sound
end Soundness

-- Completeness: Lean predicate → emitted system feasible (non-strict)
section Completeness
#check orientation_right_complete
#check orientation_left_complete
#check orientation_below_complete
#check orientation_above_complete
#check orientation_directlyRight_complete
#check orientation_directlyLeft_complete
#check orientation_directlyBelow_complete
#check orientation_directlyAbove_complete
#check align_horizontal_complete
#check align_vertical_complete
#check group₂_complete
end Completeness

-- UNSAT soundness: all 8 directions
#check unsat_soundness_orientation

-- Top-level bridge theorems (all sorry-free)
#check solver_sound_orientation
#check solver_sound_align
#check solver_complete_orientation
#check solver_complete_align

-- Cyclic bridge theorems (all sorry-free)
#check cyclic_sound
#check cyclic_complete
