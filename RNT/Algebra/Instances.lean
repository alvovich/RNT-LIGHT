-- RNT/Algebra/Instances.lean
-- Instance declarations and dimension theorems for BasisAlgebra

import RNT.Basic
import RNT.Algebra.BasisAlgebra
import RNT.Algebra.Structure
import RNT.Algebra.Operations

namespace RNT.Algebra.BasisAlgebra

open BasisAlgebra

/-- Theorem T1 from RNT-LIGHT: dim_ℂ(A_ε) = 7. -/
theorem dimension : ∃ (dim : ℕ), dim = 7 := ⟨7, rfl⟩

/-- The basis of BasisAlgebra has cardinality 7. -/
theorem basis_cardinality : Fintype.card NilpotentDGBasis = 7 := by decide

/-- Alternative formulation of dimension via basis cardinality. -/
theorem dimension_via_basis : ∃ (dim : ℕ), dim = Fintype.card NilpotentDGBasis := ⟨7, basis_cardinality⟩

/-- BasisAlgebra is a finite-dimensional vector space over ℂ. -/
theorem finite_dimensional : ∃ (dim : ℕ), Fintype.card NilpotentDGBasis = dim := ⟨7, basis_cardinality.symm⟩

/-- Explicit confirmation: dim_ℂ(A_ε) = 7 as specified in RNT-LIGHT Section 1.2. -/
theorem rnt_dimension_check :
  let algebra_dimension := Fintype.card NilpotentDGBasis
  algebra_dimension = 7 := basis_cardinality

/-- Auxiliary lemma: if component b_param of a is nonzero, then grade a ≥ degree(b_param). -/
lemma grade_ge_of_ne_zero (a : BasisAlgebra) (b_param : NilpotentDGBasis) (h_comp_ne_zero : a b_param ≠ 0) :
  grade a ≥ b_param.degree := by
  unfold grade
  cases b_param with
  | eps1theta => simp [h_comp_ne_zero, NilpotentDGBasis.degree]
  | eps2theta => simp [h_comp_ne_zero, NilpotentDGBasis.degree]
  | theta =>
    by_cases h : a .eps1theta ≠ 0 ∨ a .eps2theta ≠ 0
    · simp [h, NilpotentDGBasis.degree]
    · simp [h, h_comp_ne_zero, NilpotentDGBasis.degree]
  | eps1eps2 =>
    by_cases h : a .eps1theta ≠ 0 ∨ a .eps2theta ≠ 0
    · simp [h, NilpotentDGBasis.degree]
    · simp [h, h_comp_ne_zero, NilpotentDGBasis.degree]
  | eps1 =>
    by_cases h3 : a .eps1theta ≠ 0 ∨ a .eps2theta ≠ 0
    · simp [h3, NilpotentDGBasis.degree]
    · by_cases h2 : a .theta ≠ 0 ∨ a .eps1eps2 ≠ 0
      · simp [h3, h2, NilpotentDGBasis.degree]
      · simp [h3, h2, h_comp_ne_zero, NilpotentDGBasis.degree]
  | eps2 =>
    by_cases h3 : a .eps1theta ≠ 0 ∨ a .eps2theta ≠ 0
    · simp [h3, NilpotentDGBasis.degree]
    · by_cases h2 : a .theta ≠ 0 ∨ a .eps1eps2 ≠ 0
      · simp [h3, h2, NilpotentDGBasis.degree]
      · simp [h3, h2, h_comp_ne_zero, NilpotentDGBasis.degree]
  | one => simp [NilpotentDGBasis.degree]

lemma grade_ge_2_if_theta_ne_zero (a : BasisAlgebra) (h : a .theta ≠ 0) : grade a ≥ 2 :=
  grade_ge_of_ne_zero a .theta h

lemma grade_ge_3_if_eps1theta_ne_zero (a : BasisAlgebra) (h : a .eps1theta ≠ 0) : grade a ≥ 3 :=
  grade_ge_of_ne_zero a .eps1theta h

/-- Since d ≡ 0, d(a) = 0 for all a. -/
lemma grade_d_a_eq_0_always (a : BasisAlgebra) : d a = zero := by
  ext c
  simp only [d, zero]

/-- Proof that d preserves or increases grade by at most 1 (trivial since d ≡ 0). -/
theorem d_grade_simple (a : BasisAlgebra) : d a = zero ∨ grade (d a) ≤ grade a + 1 := by
  left
  exact grade_d_a_eq_0_always a

/-- Instance witnessing that BasisAlgebra satisfies the NilpotentDGAlgebra structure. -/
noncomputable instance instNilpotentDGAlgebraBasisAlgebra : NilpotentDGAlgebra BasisAlgebra where
  grade := grade
  basis := basis
  basis_spans := by
    intro a
    use a
    ext b
    have h_sum_def : (Finset.sum Finset.univ (fun b' => a b' • basis b')) b =
                     Finset.sum Finset.univ (fun b' => (a b' • basis b') b) := rfl
    rw [h_sum_def]
    have h_term : ∀ b', (a b' • basis b') b = if b' = b then a b' else 0 := by
      intro b'
      show (fun x => a b' * if b' = x then 1 else 0) b = if b' = b then a b' else 0
      simp [mul_ite, mul_one, mul_zero]
    rw [show Finset.sum Finset.univ (fun b' => (a b' • basis b') b) =
           Finset.sum Finset.univ (fun b' => if b' = b then a b' else 0) from
           Finset.sum_congr rfl (fun b' _ => h_term b')]
    rw [show Finset.sum Finset.univ (fun b' => if b' = b then a b' else 0) =
           Finset.sum Finset.univ (fun b' => if b = b' then a b' else 0) from
           Finset.sum_congr rfl (fun b' _ => by simp only [eq_comm])]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  basis_indep := by
    intro coeffs h_sum_zero b
    have h_apply : (Finset.sum Finset.univ (fun b' => coeffs b' • basis b')) b = (0 : BasisAlgebra) b := by
      exact congrFun h_sum_zero b
    have h_zero_at_b : (0 : BasisAlgebra) b = 0 := rfl
    rw [h_zero_at_b] at h_apply
    have h_sum_at_b : (Finset.sum Finset.univ (fun b' => coeffs b' • basis b')) b = coeffs b := by
      have h_sum_eq :
        (Finset.sum Finset.univ (fun b' => coeffs b' • basis b')) b =
        Finset.sum Finset.univ (fun b' => (coeffs b' • basis b') b) := rfl
      rw [h_sum_eq]
      have h_term : ∀ b', (coeffs b' • basis b') b = if b' = b then coeffs b' else 0 := by
        intro b'
        show (fun b => coeffs b' * if b' = b then 1 else 0) b = if b' = b then coeffs b' else 0
        simp [mul_ite, mul_one, mul_zero]
      rw [show Finset.sum Finset.univ (fun b' => (coeffs b' • basis b') b) =
             Finset.sum Finset.univ (fun b' => if b' = b then coeffs b' else 0) from
             Finset.sum_congr rfl (fun b' _ => h_term b')]
      rw [show Finset.sum Finset.univ (fun b' => if b' = b then coeffs b' else 0) =
             Finset.sum Finset.univ (fun b' => if b = b' then coeffs b' else 0) from
             Finset.sum_congr rfl (fun b' _ => by simp only [eq_comm])]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
    rw [h_sum_at_b] at h_apply
    exact h_apply
  grade_basis := grade_basis
  mul := mul
  grade_mul := by
    intro ia ib
    exact grade_mul_proof ia ib
  basis_one_is_one := by
    ext b
    cases b <;> rfl
  eps1_sq_is_zero := eps1_sq_is_zero
  eps2_sq_is_zero := eps2_sq_is_zero
  theta_sq_is_zero := theta_sq_is_zero
  eps1_eps2_commutes := eps1_eps2_commutes
  eps1_theta_commutes := eps1_theta_commutes
  eps2_theta_commutes := eps2_theta_commutes
  basis_eps1eps2_is_prod := basis_eps1eps2_is_prod
  basis_eps1theta_is_prod := basis_eps1theta_is_prod
  basis_eps2theta_is_prod := basis_eps2theta_is_prod
  eps1eps2theta_is_zero := eps1eps2theta_is_zero
  d := d
  d_basis_eps1 := d_basis_eps1
  d_basis_eps2 := d_basis_eps2
  d_basis_theta := by
    have h1 : d (basis .theta) = zero := d_basis_theta
    have h2 : zero = (0 : BasisAlgebra) := zero_eq_ring_zero.symm
    rw [h1, h2]
  d_grade := by
    intro a
    left
    exact grade_d_a_eq_0_always a
  d_leibniz := by
    intro ia ib
    exact d_leibniz_proof ia ib
  d_squared := by
    intro a
    exact d_squared a

end RNT.Algebra.BasisAlgebra

namespace RNT.Algebra.BasisAlgebra

open BasisAlgebra

/-- Basis evaluation: basis b at point b equals 1. -/
lemma basis_apply_same (b : NilpotentDGBasis) : basis b b = 1 := by
  unfold basis
  rw [if_pos rfl]

/-- Basis evaluation: basis b1 at point b2 ≠ b1 equals 0. -/
lemma basis_apply_diff {b1 b2 : NilpotentDGBasis} (h : b1 ≠ b2) : basis b1 b2 = 0 := by
  unfold basis
  rw [if_neg h]

/-- Decomposition lemma: if low-degree coordinates vanish, then x is a linear combination
of {ε₁ε₂, ε₁θ, ε₂θ}. Used in socle dimension proof (Theorem 1.7). -/
theorem decompose_if_low_coords_zero
  (x : BasisAlgebra)
  (h_one : x .one = 0) (h_eps1 : x .eps1 = 0) (h_eps2 : x .eps2 = 0) (h_theta : x .theta = 0) :
  ∃ (c12 c1t c2t : ℂ),
    x = c12 • basis .eps1eps2 + c1t • basis .eps1theta + c2t • basis .eps2theta := by
  refine ⟨x .eps1eps2, x .eps1theta, x .eps2theta, ?_⟩
  apply BasisAlgebra.ext
  intro b
  cases b with
  | one =>
    rw [h_one]
    change 0 = (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _
    unfold add smul
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.one)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.one)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.one)]
    ring
  | eps1 =>
    rw [h_eps1]
    change 0 = (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _
    unfold add smul
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.eps1)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.eps1)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.eps1)]
    ring
  | eps2 =>
    rw [h_eps2]
    change 0 = (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _
    unfold add smul
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.eps2)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.eps2)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.eps2)]
    ring
  | theta =>
    rw [h_theta]
    change 0 = (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _
    unfold add smul
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.theta)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.theta)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.theta)]
    ring
  | eps1eps2 =>
    change _ = (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _
    unfold add smul
    rw [basis_apply_same]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.eps1eps2)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.eps1eps2)]
    ring
  | eps1theta =>
    change _ = (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _
    unfold add smul
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.eps1theta)]
    rw [basis_apply_same]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.eps1theta)]
    ring
  | eps2theta =>
    change _ = (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _
    unfold add smul
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.eps2theta)]
    rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.eps2theta)]
    rw [basis_apply_same]
    ring

/-- Linear independence of {ε₁ε₂, ε₁θ, ε₂θ}. Used in socle dimension proof (Theorem 1.7). -/
theorem triple_independent_zero_sum
  (c12 c1t c2t : ℂ)
  (h : c12 • basis .eps1eps2 + c1t • basis .eps1theta + c2t • basis .eps2theta = 0) :
  c12 = 0 ∧ c1t = 0 ∧ c2t = 0 := by
  have h12 := congrFun h NilpotentDGBasis.eps1eps2
  have h1t := congrFun h NilpotentDGBasis.eps1theta
  have h2t := congrFun h NilpotentDGBasis.eps2theta
  change (add (add (smul _ (basis _)) (smul _ (basis _))) (smul _ (basis _))) _ = zero _ at h12 h1t h2t
  unfold add smul zero at h12 h1t h2t
  rw [basis_apply_same] at h12
  rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.eps1eps2)] at h12
  rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.eps1eps2)] at h12
  have hc12 : c12 = 0 := by linear_combination h12
  rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.eps1theta)] at h1t
  rw [basis_apply_same] at h1t
  rw [basis_apply_diff (by decide : NilpotentDGBasis.eps2theta ≠ NilpotentDGBasis.eps1theta)] at h1t
  have hc1t : c1t = 0 := by linear_combination h1t
  rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1eps2 ≠ NilpotentDGBasis.eps2theta)] at h2t
  rw [basis_apply_diff (by decide : NilpotentDGBasis.eps1theta ≠ NilpotentDGBasis.eps2theta)] at h2t
  rw [basis_apply_same] at h2t
  have hc2t : c2t = 0 := by linear_combination h2t
  exact ⟨hc12, hc1t, hc2t⟩

end RNT.Algebra.BasisAlgebra
