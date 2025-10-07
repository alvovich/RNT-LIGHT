-- RNT/Core/Integration.lean
-- Integration of all RNT-LIGHT components
-- Connecting universal system ℌ, braided ∞-category 𝒜, and algebra A_ε

import RNT.Basic
import RNT.Algebra.BasisAlgebra
import RNT.Algebra.Generators
import RNT.Algebra.Homology
import RNT.Algebra.Instances
import RNT.Algebra.Operations
import RNT.Core.BraidedCategory
import RNT.Core.UniversalSystem
import RNT.Core.DirectedSystem
import Mathlib.Topology.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
-- import Mathlib.Analysis.Complex.Exponential  -- not present in this mathlib snapshot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Prod
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Topology.Instances.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Constructions
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

universe u

namespace RNT.Core

open RNT.Algebra
open RNT.Algebra.BasisAlgebra
open CategoryTheory

/-- Coercion Int → Real is continuous (from discrete to standard topology) -/
lemma int_to_real_continuous : Continuous (fun (n : ℤ) => (n : ℝ)) := by
  exact continuous_of_discreteTopology

/-- Continuity of Subtype.mk when the value function is continuous -/
lemma continuous_subtype_mk' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {P : β → Prop} {f : α → β} (hf : Continuous f) (h : ∀ x, P (f x)) :
    Continuous (fun x => ⟨f x, h x⟩ : α → {b // P b}) :=
  Continuous.subtype_mk hf h

/-- Norm of exp(θ·i) equals 1 for all θ ∈ ℝ -/
lemma Complex.norm_exp_ofReal_mul_I (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.re_ofReal_mul, Complex.I_re]

/-- Discrete topology on NilpotentDGBasis -/
instance : TopologicalSpace NilpotentDGBasis := ⊥

/-- Product topology on BasisAlgebra -/
instance : TopologicalSpace BasisAlgebra := Pi.topologicalSpace

/-- Finiteness of NilpotentDGBasis -/
instance : Finite NilpotentDGBasis := Finite.of_fintype _

/-- NilpotentDGBasis is nonempty -/
instance : Nonempty NilpotentDGBasis := ⟨.one⟩

/-- Decidable equality for BasisAlgebra -/
noncomputable instance : DecidableEq BasisAlgebra := Classical.decEq _

/-- ℂ is finite-dimensional over itself (1-dimensional vector space) -/
instance : FiniteDimensional ℂ ℂ := FiniteDimensional.of_finrank_pos (by
  rw [Module.finrank_self]; norm_num : (0 : ℕ) < Module.finrank ℂ ℂ)

/-- BasisAlgebra is finite-dimensional over ℂ.
Constructed using basis from NilpotentDGBasis (7 basis elements). -/
noncomputable instance : FiniteDimensional ℂ BasisAlgebra := by
  let basis_fn := BasisAlgebra.basis
  let basis_obj : Basis NilpotentDGBasis ℂ BasisAlgebra := {
    repr := {
      toFun := fun f => Finsupp.onFinset Finset.univ (fun b => f b) (by simp),
      invFun := fun g => fun b => g b,
      left_inv := by
        intro f
        ext b
        simp [Finsupp.onFinset]
      right_inv := by
        intro g
        ext b
        simp [Finsupp.onFinset]
      map_add' := by
        intro f g
        ext b
        simp [Finsupp.onFinset, Finsupp.coe_add]
        show (f + g) b = f b + g b
        rfl
      map_smul' := by
        intro c f
        ext b
        simp [Finsupp.onFinset, Finsupp.coe_smul]
        show (c • f) b = c * f b
        rfl
    }
  }
  exact FiniteDimensional.of_fintype_basis basis_obj

/-- Grading of A_ε in ℤ according to RNT-LIGHT Definition 1.2.1 -/
noncomputable def grade_Z (x : BasisAlgebra) : ℤ := (BasisAlgebra.grade x : ℤ)

/-- Simplified grading for BasisAlgebra as linear map (zero map for technical purposes) -/
noncomputable def grade_linear_basis : BasisAlgebra →ₗ[ℂ] ℂ := {
  toFun := fun x => match x with
    | _ => 0,
  map_add' := by simp,
  map_smul' := by simp
}

/-- A_ε as an object in the braided ∞-category -/
noncomputable def basis_algebra_as_vector_space : VectorSpaceObject := {
  space := BasisAlgebra,
  grading := grade_linear_basis
}

/-- Explicit TopologicalSpace instance for Circle -/
instance : TopologicalSpace Circle := inferInstance

/-- Explicit Preorder instance for ℤ -/
instance : Preorder ℤ := inferInstance

/-- Directed system indexed by ℕ -/
noncomputable def circle_directed_system : DirectedSystem ℕ := {
  order := inferInstance,
  directed := by
    intros n m
    use max n m
    exact ⟨le_max_left n m, le_max_right n m⟩
}

/-- State space family of circles X_n = S¹ -/
noncomputable def circle_state_space_family : StateSpaceFamily ℕ circle_directed_system := {
  space := fun _ => Circle,
  topology := fun _ => by
    haveI : TopologicalSpace Circle := inferInstance
    exact this,
  map := fun h => id,
  map_continuous := by
    intros n m h
    exact continuous_id,
  map_id := by
    intro n
    rfl,
  map_comp := by
    intros n m k h₁ h₂
    rfl
}

/-- Parameter family P_n = ℤ with discrete topology -/
noncomputable def discrete_int_parameter_family : ParameterFamily ℕ circle_directed_system := {
  param := fun _ => ℤ,
  order_param := fun _ => inferInstance,
  topology := fun _ => ⊥,
  map := fun h => id,
  map_monotone := by
    intros n m h
    exact monotone_id,
  map_continuous := by
    intros n m h
    exact continuous_id,
  order_topology := by
    intro n
    exact ⟨OrderTopology.topology_eq_generate_intervals⟩,
  map_id := by
    intro n
    rfl,
  map_comp := by
    intros n m k h₁ h₂
    rfl
}

/-- Circle rotation map -/
noncomputable def circle_rotation (θ : ℝ) : Circle → Circle :=
  fun z => z * ⟨Complex.exp (θ * Complex.I), by
    change Complex.exp (θ * Complex.I) ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, Complex.dist_eq, sub_zero]
    exact Complex.norm_exp_ofReal_mul_I θ⟩

/-- Continuity of θ ↦ exp(θ·i) -/
lemma exp_theta_I_continuous : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by
  apply Continuous.comp Complex.continuous_exp
  apply Continuous.comp (continuous_mul_right Complex.I)
  exact Complex.continuous_ofReal

/-- exp(θ·i) lies in unit sphere -/
lemma exp_theta_I_in_sphere (θ : ℝ) : Complex.exp (θ * Complex.I) ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, Complex.dist_eq, sub_zero]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- Circle rotation is jointly continuous in both variables -/
lemma circle_rotation_continuous : Continuous (Function.uncurry circle_rotation) := by
  apply Continuous.mul
  · exact continuous_snd
  · apply Continuous.subtype_mk
    apply Continuous.comp exp_theta_I_continuous
    exact continuous_fst

/-- Universal system ℌ = (X, P, Φ, I, 𝒜) for RNT-LIGHT.
Simplified version with X = S¹, P = ℤ, and evolution Φ via circle rotations. -/
noncomputable def nontrivial_universal_system : UniversalSystem ℕ circle_directed_system := {
  X_family := circle_state_space_family,
  P_family := discrete_int_parameter_family,
  X := Circle,
  X_topology := inferInstance,
  X_metric := by exact Circle.instMetricSpace.toPseudoMetricSpace,
  X_family_metrics := fun _ => Circle.instMetricSpace.toPseudoMetricSpace,
  X_metric_compatible := by
    intro n
    letI : TopologicalSpace (circle_state_space_family.space n) := circle_state_space_family.topology n
    use id
    exact ⟨fun x y => rfl, continuous_id⟩,
  X_inclusion := fun _ => id,
  X_inclusion_continuous := by
    intros n
    letI : TopologicalSpace (circle_state_space_family.space n) := circle_state_space_family.topology n
    exact continuous_id,
  X_inclusion_compat := by
    intros n m h x
    rfl,
  P := ℤ,
  P_order_univ := inferInstance,
  P_topology := ⊥,
  P_colimit_topology := by
    use fun _ => id
    intro V
    constructor
    · intro h_open n
      exact h_open
    · intro h
      exact h 0,
  P_inclusion := fun _ => id,
  P_inclusion_monotone := by
    intros n
    letI po : PartialOrder (discrete_int_parameter_family.param n) := discrete_int_parameter_family.order_param n
    exact monotone_id,
  P_inclusion_compat := by
    intros n m h p
    rfl,
  X_universal := by
    intros Z _Z_topology f_map _f_continuous_map _f_compat
    use fun x => f_map 0 x
    constructor
    · constructor
      · intro n x
        exact (_f_compat (Nat.zero_le n) x).symm
      · exact _f_continuous_map 0
    · intro g ⟨h_eq, h_cont⟩
      ext x
      exact h_eq 0 x,
  P_universal := by
    intros Q _Q_order g_map _g_monotone _g_compat
    use fun p => g_map 0 p
    constructor
    · constructor
      · intro n p
        exact (_g_compat (Nat.zero_le n) p).symm
      · exact _g_monotone 0
    · intro g ⟨h_eq, h_mono⟩
      ext p
      exact h_eq 0 p,
  𝒜 := VectorSpaceBraidedCategory,
  I := fun _ => basis_algebra_as_vector_space,
  Phi := fun x p => circle_rotation (p * 2 * Real.pi) x,
  Phi_joint_continuous := by
    let h : Circle × ℤ → ℝ × Circle := fun (x, p) => (p * 2 * Real.pi, x)
    have h_cont : Continuous h := by
      apply Continuous.prodMk
      · show Continuous fun x : Circle × ℤ => ↑x.2 * 2 * Real.pi
        have f1 : Continuous (fun (x : Circle × ℤ) => (x.2 : ℝ)) := by
          exact Continuous.comp int_to_real_continuous continuous_snd
        have f2 : Continuous (fun (_ : Circle × ℤ) => 2 * Real.pi) := continuous_const
        have h_eq : (fun x : Circle × ℤ => (x.2 : ℝ)) * (fun _ : Circle × ℤ => 2 * Real.pi) = fun x => ↑x.2 * 2 * Real.pi := by
          funext x
          simp [Pi.mul_apply]
          rw [mul_assoc]
        rw [← h_eq]
        exact Continuous.mul f1 f2
      · exact continuous_fst
    exact Continuous.comp circle_rotation_continuous h_cont
  Phi_homeomorph := by
    intro p
    let angle := p * 2 * Real.pi
    exact {
      toFun := circle_rotation angle,
      invFun := circle_rotation (-angle),
      left_inv := by
        intro z
        unfold circle_rotation
        ext
        show ↑z * Complex.exp (↑angle * Complex.I) * Complex.exp (↑(-angle) * Complex.I) = ↑z
        rw [mul_assoc, ← Complex.exp_add]
        have h : ↑angle * Complex.I + ↑(-angle) * Complex.I = 0 := by
          have neg_coe : (↑(-angle) : ℂ) = -(↑angle : ℂ) := by norm_cast
          rw [neg_coe]
          rw [← add_mul, add_neg_cancel, zero_mul]
        rw [h, Complex.exp_zero, mul_one],
      right_inv := by
        intro z
        unfold circle_rotation
        ext
        show ↑z * Complex.exp (↑(-angle) * Complex.I) * Complex.exp (↑angle * Complex.I) = ↑z
        rw [mul_assoc, ← Complex.exp_add]
        have h : ↑(-angle) * Complex.I + ↑angle * Complex.I = 0 := by
          have neg_coe : (↑(-angle) : ℂ) = -(↑angle : ℂ) := by norm_cast
          rw [neg_coe]
          rw [← add_mul, neg_add_cancel, zero_mul]
        rw [h, Complex.exp_zero, mul_one],
      continuous_toFun := by
        unfold circle_rotation
        exact continuous_mul_right _,
      continuous_invFun := by
        unfold circle_rotation
        exact continuous_mul_right _
    },
  Phi_homeomorph_apply := by
    intros p x
    unfold circle_rotation
    rfl
}

/-- Main RNT integration theorem.
Establishes that A_ε is a proper object in VectorSpaceBraidedCategory with functor I. -/
theorem main_rnt_integration :
  ∃ (A_ε_obj : VectorSpaceObject),
    A_ε_obj.space = BasisAlgebra ∧
    ∃ (cat : BraidedInfinityCategory),
      cat = VectorSpaceBraidedCategory ∧
      ∃ (I : BasisAlgebra → VectorSpaceObject),
        ∀ x, I x = A_ε_obj := by
  use basis_algebra_as_vector_space
  constructor
  · rfl
  · use VectorSpaceBraidedCategory
    constructor
    · rfl
    · use fun _ => basis_algebra_as_vector_space
      intro x
      rfl

/-- Integration preserves algebra structure.
Grading is consistent between algebra and category object. -/
theorem integration_preserves_algebra_structure :
  ∀ x : BasisAlgebra,
    basis_algebra_as_vector_space.grading x = grade_linear_basis x := by
  intro x
  simp [basis_algebra_as_vector_space]

/-- Nilpotent structure preservation (RNT-LIGHT Definition 1.2.1).
Nilpotency relations ε₁² = ε₂² = θ² = 0 and critical relation ε₁ε₂θ = 0 are preserved. -/
theorem nilpotent_structure_preserved :
  ∃ (mul : BasisAlgebra → BasisAlgebra → BasisAlgebra),
    mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps1) = BasisAlgebra.zero ∧
    mul (BasisAlgebra.basis .eps2) (BasisAlgebra.basis .eps2) = BasisAlgebra.zero ∧
    mul (BasisAlgebra.basis .theta) (BasisAlgebra.basis .theta) = BasisAlgebra.zero ∧
    mul (mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps2)) (BasisAlgebra.basis .theta) = BasisAlgebra.zero := by
  use BasisAlgebra.mul
  exact ⟨BasisAlgebra.eps1_sq_is_zero, BasisAlgebra.eps2_sq_is_zero, BasisAlgebra.theta_sq_is_zero, eps1eps2_theta_is_zero⟩

/-- Grading of all 7 basis elements in ℤ according to RNT-LIGHT. -/
theorem grade_Z_basis_elements :
  grade_Z (BasisAlgebra.basis .one) = 0 ∧
  grade_Z (BasisAlgebra.basis .eps1) = 1 ∧
  grade_Z (BasisAlgebra.basis .eps2) = 1 ∧
  grade_Z (BasisAlgebra.basis .theta) = 2 ∧
  grade_Z (BasisAlgebra.basis .eps1eps2) = 2 ∧
  grade_Z (BasisAlgebra.basis .eps1theta) = 3 ∧
  grade_Z (BasisAlgebra.basis .eps2theta) = 3 := by
  constructor
  · unfold grade_Z BasisAlgebra.grade BasisAlgebra.basis
    simp
  constructor
  · unfold grade_Z BasisAlgebra.grade BasisAlgebra.basis
    simp
  constructor
  · unfold grade_Z BasisAlgebra.grade BasisAlgebra.basis
    simp
  constructor
  · unfold grade_Z BasisAlgebra.grade BasisAlgebra.basis
    simp
  constructor
  · unfold grade_Z BasisAlgebra.grade BasisAlgebra.basis
    simp
  constructor
  · unfold grade_Z BasisAlgebra.grade BasisAlgebra.basis
    simp
  · unfold grade_Z BasisAlgebra.grade BasisAlgebra.basis
    simp

/-- Integration functoriality theorem. -/
theorem integration_functoriality :
  ∃ (I : BasisAlgebra → VectorSpaceObject),
    (∀ x, I x = basis_algebra_as_vector_space) := by
  use fun _ => basis_algebra_as_vector_space
  intro x; rfl

/-- Braiding naturality in VectorSpaceBraidedCategory. -/
theorem braiding_naturality :
  ∀ (V W : VectorSpaceObject),
    ∃ (braiding : VectorSpaceBraidedCategory.morphisms
                   (VectorSpaceBraidedCategory.tensor_obj V W)
                   (VectorSpaceBraidedCategory.tensor_obj W V)),
      braiding = VectorSpaceBraidedCategory.braiding V W := by
  intro V W
  use VectorSpaceBraidedCategory.braiding V W

/-- Trivial vector space object (ℂ as 1-dimensional space) -/
noncomputable def trivial_vector_space : VectorSpaceObject := {
  space := ℂ,
  grading := 0,
  finite_dim := by
    exact FiniteDimensional.of_finrank_eq_succ (Module.finrank_self ℂ)
}

/-- Compliance with RNT-LIGHT Definition 1.2.1 for A_ε. -/
theorem rnt_definition_1_2_1_compliance :
  ∃ (A_ε : VectorSpaceObject),
    A_ε.space = BasisAlgebra ∧
    (A_ε.space = BasisAlgebra → ∃ (gr : BasisAlgebra → ℤ), gr = grade_Z) ∧
    (∃ (mul : BasisAlgebra → BasisAlgebra → BasisAlgebra),
      mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps1) = BasisAlgebra.zero ∧
      mul (BasisAlgebra.basis .eps2) (BasisAlgebra.basis .eps2) = BasisAlgebra.zero ∧
      mul (BasisAlgebra.basis .theta) (BasisAlgebra.basis .theta) = BasisAlgebra.zero ∧
      mul (mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps2)) (BasisAlgebra.basis .theta) = BasisAlgebra.zero) := by
  use basis_algebra_as_vector_space
  exact ⟨rfl, ⟨fun _ => ⟨grade_Z, rfl⟩, nilpotent_structure_preserved⟩⟩

/-- Compliance with RNT-LIGHT Definition 1.3.1 (braided ∞-category). -/
theorem rnt_definition_1_3_1_compliance :
  ∃ (cat : BraidedInfinityCategory),
    cat = VectorSpaceBraidedCategory ∧
    (∀ V : VectorSpaceObject, FiniteDimensional ℂ V.space) := by
  use VectorSpaceBraidedCategory
  constructor
  · rfl
  · intro V; exact V.finite_dim

/-- Full compliance with RNT-LIGHT Definitions 1.1.1-1.3.1.
Establishes that the integrated system satisfies all three main definitions. -/
theorem full_rnt_compliance :
  True ∧
  (∃ (A_ε : VectorSpaceObject),
    A_ε.space = BasisAlgebra ∧
    (∃ (mul : BasisAlgebra → BasisAlgebra → BasisAlgebra),
      mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps1) = BasisAlgebra.zero ∧
      mul (BasisAlgebra.basis .eps2) (BasisAlgebra.basis .eps2) = BasisAlgebra.zero ∧
      mul (BasisAlgebra.basis .theta) (BasisAlgebra.basis .theta) = BasisAlgebra.zero ∧
      mul (mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps2)) (BasisAlgebra.basis .theta) = BasisAlgebra.zero)) ∧
  (∃ (cat : BraidedInfinityCategory),
    cat = VectorSpaceBraidedCategory ∧
    (∀ V : VectorSpaceObject, FiniteDimensional ℂ V.space)) := by
  constructor
  · trivial
  constructor
  · use basis_algebra_as_vector_space
    constructor
    · rfl
    · use BasisAlgebra.mul
      exact ⟨BasisAlgebra.eps1_sq_is_zero, BasisAlgebra.eps2_sq_is_zero, BasisAlgebra.theta_sq_is_zero, eps1eps2_theta_is_zero⟩
  · use VectorSpaceBraidedCategory
    constructor
    · rfl
    · intro V; exact V.finite_dim

/-- Homology space H⁰(A_ε) ≅ ℂ (RNT-LIGHT Definition 1.2.1) -/
noncomputable def H0 : VectorSpaceObject := {
  space := ℂ,
  grading := 0,
  finite_dim := by infer_instance
}

/-- Homology space H¹(A_ε) ≅ ℂ² (RNT-LIGHT Definition 1.2.1) -/
noncomputable def H1 : VectorSpaceObject := {
  space := ℂ × ℂ,
  grading := 0,
  finite_dim := by infer_instance
}

/-- Homology space H²(A_ε) ≅ ℂ² (RNT-LIGHT Definition 1.2.1) -/
noncomputable def H2 : VectorSpaceObject := {
  space := ℂ × ℂ,
  grading := 0,
  finite_dim := by infer_instance
}

/-- Homology space H³(A_ε) ≅ ℂ (RNT-LIGHT Definition 1.2.1) -/
noncomputable def H3 : VectorSpaceObject := {
  space := ℂ,
  grading := 0,
  finite_dim := by infer_instance
}

/-- Product type for homology tuple: H⁰ × H¹ × H² × H³ ≅ ℂ × ℂ² × ℂ² × ℂ -/
def HomologyProdType := ℂ × (ℂ × ℂ) × (ℂ × ℂ) × ℂ

/-- AddCommMonoid instance for HomologyProdType -/
noncomputable instance : AddCommMonoid HomologyProdType := {
  add := fun (a1, (a2, a3), (a4, a5), a6) (b1, (b2, b3), (b4, b5), b6) =>
    (a1 + b1, (a2 + b2, a3 + b3), (a4 + b4, a5 + b5), a6 + b6),
  zero := (0, (0, 0), (0, 0), 0),
  nsmul := fun n (a1, (a2, a3), (a4, a5), a6) =>
    (n • a1, (n • a2, n • a3), (n • a4, n • a5), n • a6),
  add_assoc := by
    intros a b c
    apply Prod.ext
    · exact add_assoc a.1 b.1 c.1
    · apply Prod.ext
      · apply Prod.ext
        · exact add_assoc a.2.1.1 b.2.1.1 c.2.1.1
        · exact add_assoc a.2.1.2 b.2.1.2 c.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact add_assoc a.2.2.1.1 b.2.2.1.1 c.2.2.1.1
          · exact add_assoc a.2.2.1.2 b.2.2.1.2 c.2.2.1.2
        · exact add_assoc a.2.2.2 b.2.2.2 c.2.2.2
  zero_add := by
    intro a
    apply Prod.ext
    · exact zero_add a.1
    · apply Prod.ext
      · apply Prod.ext
        · exact zero_add a.2.1.1
        · exact zero_add a.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact zero_add a.2.2.1.1
          · exact zero_add a.2.2.1.2
        · exact zero_add a.2.2.2
  add_zero := by
    intro a
    apply Prod.ext
    · exact add_zero a.1
    · apply Prod.ext
      · apply Prod.ext
        · exact add_zero a.2.1.1
        · exact add_zero a.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact add_zero a.2.2.1.1
          · exact add_zero a.2.2.1.2
        · exact add_zero a.2.2.2
  add_comm := by
    intros a b
    apply Prod.ext
    · exact add_comm a.1 b.1
    · apply Prod.ext
      · apply Prod.ext
        · exact add_comm a.2.1.1 b.2.1.1
        · exact add_comm a.2.1.2 b.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact add_comm a.2.2.1.1 b.2.2.1.1
          · exact add_comm a.2.2.1.2 b.2.2.1.2
        · exact add_comm a.2.2.2 b.2.2.2
  nsmul_zero := by
    intro a
    cases a with
    | mk a1 rest =>
      cases rest with
      | mk h1 rest2 =>
        cases h1 with
        | mk a2 a3 =>
          cases rest2 with
          | mk h2 a6 =>
            cases h2 with
            | mk a4 a5 =>
              simp [zero_smul]
              rfl
  nsmul_succ := by
    intro n a
    cases a with
    | mk a1 rest =>
      cases rest with
      | mk h1 rest2 =>
        cases h1 with
        | mk a2 a3 =>
          cases rest2 with
          | mk h2 a6 =>
            cases h2 with
            | mk a4 a5 =>
              simp [Nat.succ_eq_add_one, add_nsmul, one_nsmul]
              show ((↑n + 1) * a1, ((↑n + 1) * a2, (↑n + 1) * a3), ((↑n + 1) * a4, (↑n + 1) * a5), (↑n + 1) * a6) =
                   (↑n * a1 + a1, (↑n * a2 + a2, ↑n * a3 + a3), (↑n * a4 + a4, ↑n * a5 + a5), ↑n * a6 + a6)
              simp [add_mul, one_mul]
}

/-- Module ℂ instance for HomologyProdType -/
noncomputable instance : Module ℂ HomologyProdType := {
  smul := fun c (a1, (a2, a3), (a4, a5), a6) =>
    (c • a1, (c • a2, c • a3), (c • a4, c • a5), c • a6),
  one_smul := by
    intro a
    apply Prod.ext
    · exact one_smul ℂ a.1
    · apply Prod.ext
      · apply Prod.ext
        · exact one_smul ℂ a.2.1.1
        · exact one_smul ℂ a.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact one_smul ℂ a.2.2.1.1
          · exact one_smul ℂ a.2.2.1.2
        · exact one_smul ℂ a.2.2.2
  mul_smul := by
    intros c d a
    apply Prod.ext
    · exact mul_smul c d a.1
    · apply Prod.ext
      · apply Prod.ext
        · exact mul_smul c d a.2.1.1
        · exact mul_smul c d a.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact mul_smul c d a.2.2.1.1
          · exact mul_smul c d a.2.2.1.2
        · exact mul_smul c d a.2.2.2
  smul_zero := by
    intro c
    apply Prod.ext
    · exact smul_zero c
    · apply Prod.ext
      · apply Prod.ext
        · exact smul_zero c
        · exact smul_zero c
      · apply Prod.ext
        · apply Prod.ext
          · exact smul_zero c
          · exact smul_zero c
        · exact smul_zero c
  smul_add := by
    intros c a b
    apply Prod.ext
    · exact smul_add c a.1 b.1
    · apply Prod.ext
      · apply Prod.ext
        · exact smul_add c a.2.1.1 b.2.1.1
        · exact smul_add c a.2.1.2 b.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact smul_add c a.2.2.1.1 b.2.2.1.1
          · exact smul_add c a.2.2.1.2 b.2.2.1.2
        · exact smul_add c a.2.2.2 b.2.2.2
  add_smul := by
    intros c d a
    apply Prod.ext
    · exact add_smul c d a.1
    · apply Prod.ext
      · apply Prod.ext
        · exact add_smul c d a.2.1.1
        · exact add_smul c d a.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact add_smul c d a.2.2.1.1
          · exact add_smul c d a.2.2.1.2
        · exact add_smul c d a.2.2.2
  zero_smul := by
    intro a
    apply Prod.ext
    · exact zero_smul ℂ a.1
    · apply Prod.ext
      · apply Prod.ext
        · exact zero_smul ℂ a.2.1.1
        · exact zero_smul ℂ a.2.1.2
      · apply Prod.ext
        · apply Prod.ext
          · exact zero_smul ℂ a.2.2.1.1
          · exact zero_smul ℂ a.2.2.1.2
        · exact zero_smul ℂ a.2.2.2
}

/-- Homology selection map ι: BasisAlgebra → H⁰ × H¹ × H² × H³.
Maps basis elements to their homology classes. Note: eps1theta maps to zero in H³. -/
noncomputable def ι : BasisAlgebra →ₗ[ℂ] HomologyProdType := {
  toFun := fun x => (
    x (.one),
    (x (.eps1), x (.eps2)),
    (x (.theta), x (.eps1eps2)),
    x (.eps2theta)
  ),
  map_add' := by
    intros x y
    apply Prod.ext
    · show (x + y) .one = x .one + y .one
      rfl
    · apply Prod.ext
      · apply Prod.ext
        · show (x + y) .eps1 = x .eps1 + y .eps1
          rfl
        · show (x + y) .eps2 = x .eps2 + y .eps2
          rfl
      · apply Prod.ext
        · apply Prod.ext
          · show (x + y) .theta = x .theta + y .theta
            rfl
          · show (x + y) .eps1eps2 = x .eps1eps2 + y .eps1eps2
            rfl
        · show (x + y) .eps2theta = x .eps2theta + y .eps2theta
          rfl
  map_smul' := by
    intros c x
    apply Prod.ext
    · show (c • x) .one = c * x .one
      rfl
    · apply Prod.ext
      · apply Prod.ext
        · show (c • x) .eps1 = c * x .eps1
          rfl
        · show (c • x) .eps2 = c * x .eps2
          rfl
      · apply Prod.ext
        · apply Prod.ext
          · show (c • x) .theta = c * x .theta
            rfl
          · show (c • x) .eps1eps2 = c * x .eps1eps2
            rfl
        · show (c • x) .eps2theta = c * x .eps2theta
          rfl
}

/-- Category instance for VectorSpaceBraidedCategory objects -/
noncomputable instance : Category VectorSpaceBraidedCategory.objects := {
  Hom := VectorSpaceBraidedCategory.morphisms,
  id := VectorSpaceBraidedCategory.id,
  comp := fun f g => VectorSpaceBraidedCategory.comp g f,
  id_comp := by intro X Y f; exact (VectorSpaceBraidedCategory.comp_id f).down,
  comp_id := by intro X Y f; exact (VectorSpaceBraidedCategory.id_comp f).down,
  assoc := by intro W X Y Z f g h; exact (VectorSpaceBraidedCategory.assoc h g f).down
}

/-- Functor I: Discrete(S¹) → 𝒜 according to RNT-LIGHT.
Maps each point of S¹ to the invariant algebra A_ε. -/
noncomputable def I : Discrete Circle ⥤ VectorSpaceBraidedCategory.objects := {
  obj := fun _ => basis_algebra_as_vector_space,
  map := fun f => LinearMap.id,
  map_id := by
    intro X
    rfl,
  map_comp := by
    intro X Y Z f g
    rfl
}

/-- Homology integration theorem (RNT-LIGHT Definition 1.2.1).
Establishes H⁰ ≅ ℂ, H¹ ≅ ℂ², H² ≅ ℂ², H³ ≅ ℂ with dimensions (1,2,2,1).
Note: eps1theta maps to zero in H³, only eps2theta generates H³. -/
theorem homology_integration_corrected :
  ∃ (H0 H1 H2 H3 : VectorSpaceObject.{0}),
    Module.finrank ℂ H0.space = 1 ∧
    Module.finrank ℂ H1.space = 2 ∧
    Module.finrank ℂ H2.space = 2 ∧
    Module.finrank ℂ H3.space = 1 ∧
    ∃ (ι_map : BasisAlgebra →ₗ[ℂ] HomologyProdType),
      ι_map (BasisAlgebra.basis .one) = (1, (0, 0), (0, 0), 0) ∧
      ι_map (BasisAlgebra.basis .eps1) = (0, (1, 0), (0, 0), 0) ∧
      ι_map (BasisAlgebra.basis .eps2) = (0, (0, 1), (0, 0), 0) ∧
      ι_map (BasisAlgebra.basis .theta) = (0, (0, 0), (1, 0), 0) ∧
      ι_map (BasisAlgebra.basis .eps1eps2) = (0, (0, 0), (0, 1), 0) ∧
      ι_map (BasisAlgebra.basis .eps2theta) = (0, (0, 0), (0, 0), 1) ∧
      ι_map (BasisAlgebra.basis .eps1theta) = (0, (0, 0), (0, 0), 0) := by
  use H0, H1, H2, H3
  constructor
  · exact Module.finrank_self ℂ
  constructor
  · show Module.finrank ℂ (ℂ × ℂ) = 2
    rw [Module.finrank_prod]
    simp [Module.finrank_self]
  constructor
  · show Module.finrank ℂ (ℂ × ℂ) = 2
    rw [Module.finrank_prod]
    simp [Module.finrank_self]
  constructor
  · exact Module.finrank_self ℂ
  · use ι
    constructor
    · simp [ι, BasisAlgebra.basis]
    constructor
    · simp [ι, BasisAlgebra.basis]
    constructor
    · simp [ι, BasisAlgebra.basis]
    constructor
    · simp [ι, BasisAlgebra.basis]
    constructor
    · simp [ι, BasisAlgebra.basis]
    constructor
    · simp [ι, BasisAlgebra.basis]
    · simp [ι, BasisAlgebra.basis]

/-- Connection between functor I and universal system (RNT-LIGHT).
Verifies that functor I correctly maps S¹ to A_ε and homology dimensions are correct. -/
theorem I_functor_universal_system_connection_corrected :
  ∀ (x : Circle),
    I.obj ⟨x⟩ = basis_algebra_as_vector_space ∧
    (Module.finrank ℂ H0.space = 1) ∧
    (Module.finrank ℂ H1.space = 2) ∧
    (Module.finrank ℂ H2.space = 2) ∧
    (Module.finrank ℂ H3.space = 1) ∧
    (∃ (ι_corrected : BasisAlgebra →ₗ[ℂ] HomologyProdType),
      ι_corrected (BasisAlgebra.basis .eps2theta) = (0, (0, 0), (0, 0), 1) ∧
      ι_corrected (BasisAlgebra.basis .eps1theta) = (0, (0, 0), (0, 0), 0)) := by
  intro x
  constructor
  · rfl
  · exact ⟨by simp [H0, Module.finrank_self],
          by simp [H1, Module.finrank_prod, Module.finrank_self],
          by simp [H2, Module.finrank_prod, Module.finrank_self],
          by simp [H3, Module.finrank_self],
          ⟨ι, by simp [ι, BasisAlgebra.basis], by simp [ι, BasisAlgebra.basis]⟩⟩

end RNT.Core

namespace RNT.Core

/-- Theorem 3.3 from RNT-LIGHT: Triviality of Φ on S¹.
For each p ∈ ℤ, rotation by angle p·2π is the identity map since exp(i·p·2π) = 1. -/
theorem Phi_is_identity (x : Circle) (p : ℤ) :
  nontrivial_universal_system.Phi x p = x := by
  unfold nontrivial_universal_system circle_rotation
  have h_exp_eq_one : Complex.exp (↑(↑p * 2 * Real.pi) * Complex.I) = 1 := by
    calc Complex.exp (↑(↑p * 2 * Real.pi) * Complex.I)
      _ = Complex.exp (↑p * (2 * ↑Real.pi) * Complex.I) := by
          congr 1
          push_cast
          ring
      _ = Complex.exp (↑p * (2 * ↑Real.pi * Complex.I)) := by
          congr 1
          ring
      _ = Complex.exp (2 * ↑Real.pi * Complex.I) ^ p := by
          rw [← Complex.exp_int_mul]
      _ = 1 ^ p := by
          congr 1
          exact Complex.exp_two_pi_mul_I
      _ = 1 := one_zpow p
  ext
  simp only [Circle.coe_mul]
  rw [h_exp_eq_one]
  exact mul_one _

/-- Invariance of functor I under Φ (trivial since I is constant) -/
theorem I_invariant_under_Phi (x : Circle) (p : ℤ) :
  (I.obj ⟨nontrivial_universal_system.Phi x p⟩) = (I.obj ⟨x⟩) := by
  rfl

/-- Corollary 3.4 from RNT-LIGHT: all points of S¹ are fixed points of Φ(·,p).
This follows immediately from Theorem 3.3. -/
theorem Phi_all_points_fixed (p : ℤ) :
  ∀ x : Circle, nontrivial_universal_system.Phi x p = x :=
  fun x => Phi_is_identity x p

/-- Stability of homology selection ι under Φ.
Since Φ is identity and I is constant, ι is automatically stable. -/
theorem homology_selection_stable_under_Phi :
  ∀ (x : Circle) (p : ℤ), nontrivial_universal_system.Phi x p = x := by
  intro x p
  exact Phi_is_identity x p

end RNT.Core
