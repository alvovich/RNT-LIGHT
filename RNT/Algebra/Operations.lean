-- RNT/Algebra/Operations.lean
-- Operations and properties for BasisAlgebra

import RNT.Basic
import RNT.Algebra.Generators
import RNT.Algebra.BasisAlgebra

namespace RNT.Algebra.BasisAlgebra

open BasisAlgebra

/-- Grading compatibility with multiplication (RNT-LIGHT Theorem T2).
For basis elements, either their product is zero (due to nilpotency) or the grade is additive.
This theorem exhaustively verifies all 49 = 7×7 combinations of basis element products. -/
theorem grade_mul_proof : ∀ (ia ib : NilpotentDGBasis),
    mul (basis ia) (basis ib) = zero ∨ grade (mul (basis ia) (basis ib)) = (NilpotentDGBasis.degree ia) + (NilpotentDGBasis.degree ib) := by
  intro ia ib
  match ia, ib with
  -- Unit cases: multiplication with 1
  | .one, b => right; simp [NilpotentDGBasis.degree]; exact (grade_mul_with_one b).1
  | a, .one => right; simp [NilpotentDGBasis.degree]; exact (grade_mul_with_one a).2

  -- Nilpotency: squares vanish (Theorem T2)
  | .eps1, .eps1 => left; exact eps1_sq_is_zero
  | .eps2, .eps2 => left; exact eps2_sq_is_zero
  | .theta, .theta => left; exact theta_sq_is_zero

  -- Products yielding degree 2 elements
  | .eps1, .eps2 =>
    right
    -- Goal: grade(ε₁ε₂) = 1 + 1
    simp_all only [dot_mul_eq_mul_function, basis_eps1eps2_is_prod.symm, grade_basis, NilpotentDGBasis.degree]
  | .eps2, .eps1 =>
    right
    -- Use commutativity: ε₂ε₁ = ε₁ε₂
    convert_to ((basis .eps1).mul (basis .eps2)).grade = 1 + 1 using 1
    · rw [dot_mul_eq_mul_function, dot_mul_eq_mul_function, eps1_eps2_commutes]
    · simp_all only [dot_mul_eq_mul_function, basis_eps1eps2_is_prod.symm, grade_basis, NilpotentDGBasis.degree]

  -- Products yielding degree 3 elements
  | .eps1, .theta =>
    right
    simp_all only [dot_mul_eq_mul_function, basis_eps1theta_is_prod.symm, grade_basis, NilpotentDGBasis.degree]
  | .theta, .eps1 =>
    right
    -- Use commutativity: θε₁ = ε₁θ
    convert_to ((basis .eps1).mul (basis .theta)).grade = 2 + 1 using 1
    · rw [dot_mul_eq_mul_function, dot_mul_eq_mul_function, eps1_theta_commutes]
    · simp_all only [dot_mul_eq_mul_function, basis_eps1theta_is_prod.symm, grade_basis, NilpotentDGBasis.degree]
  | .eps2, .theta =>
    right
    simp_all only [dot_mul_eq_mul_function, basis_eps2theta_is_prod.symm, grade_basis, NilpotentDGBasis.degree]
  | .theta, .eps2 =>
    right
    -- Use commutativity: θε₂ = ε₂θ
    convert_to ((basis .eps2).mul (basis .theta)).grade = 1 + 2 using 1
    · rw [dot_mul_eq_mul_function, dot_mul_eq_mul_function, eps2_theta_commutes]
    · simp_all only [dot_mul_eq_mul_function, basis_eps2theta_is_prod.symm, grade_basis, NilpotentDGBasis.degree]

  -- Products involving ε₁ε₂θ = 0 (critical relation from RNT-LIGHT Section 1.1)
  | .eps1eps2, .theta => left; ext b; cases b <;> simp [mul, basis, zero]
  | .theta, .eps1eps2 => left; ext b; cases b <;> simp [mul, basis, zero]
  | .eps1, .eps2theta => left; ext b; cases b <;> simp [mul, basis, zero]
  | .eps2theta, .eps1 => left; ext b; cases b <;> simp [mul, basis, zero]
  | .eps2, .eps1theta => left; ext b; cases b <;> simp [mul, basis, zero]
  | .eps1theta, .eps2 => left; ext b; cases b <;> simp [mul, basis, zero]

  -- Higher-order nilpotent products
  | .eps1eps2, .eps1 => left; exact eps1eps2_mul_eps1_is_zero
  | .eps1, .eps1eps2 => left; exact eps1_mul_eps1eps2_is_zero
  | .eps1eps2, .eps2 => left; ext b; cases b <;> simp [mul, basis, zero]
  | .eps2, .eps1eps2 => left; ext b; cases b <;> simp [mul, basis, zero]
  | .eps1, .eps1theta => left; exact mul_eps1_eps1theta
  | .eps1theta, .eps1 => left; exact mul_eps1theta_eps1
  | .eps2, .eps2theta => left; exact mul_eps2_eps2theta
  | .eps2theta, .eps2 => left; exact mul_eps2theta_eps2

  | .theta, .eps1theta => left; exact mul_theta_eps1theta
  | .eps1theta, .theta => left; exact mul_eps1theta_theta
  | .theta, .eps2theta => left; exact mul_theta_eps2theta
  | .eps2theta, .theta => left; exact mul_eps2theta_theta

  | .eps1eps2, .eps1theta => left; exact mul_eps1eps2_eps1theta
  | .eps1theta, .eps1eps2 => left; exact mul_eps1theta_eps1eps2
  | .eps1eps2, .eps2theta => left; exact mul_eps1eps2_eps2theta
  | .eps2theta, .eps1eps2 => left; exact mul_eps2theta_eps1eps2
  | .eps1eps2, .eps1eps2 => left; ext b; cases b <;> simp [mul, basis, zero]

  | .eps1theta, .eps2theta => left; exact mul_eps1theta_eps2theta
  | .eps2theta, .eps1theta => left; exact mul_eps2theta_eps1theta
  | .eps1theta, .eps1theta => left; ext b; cases b <;> simp [mul, basis, zero]
  | .eps2theta, .eps2theta => left; ext b; cases b <;> simp [mul, basis, zero]

/-- Leibniz rule for the differential (RNT-LIGHT Theorem T3).
The differential satisfies d(ab) = da·b + (-1)^|a|·a·db.
In RNT-LIGHT, d ≡ 0 (trivial differential), so this reduces to 0 = 0 + 0.
This theorem exhaustively verifies the identity for all 49 = 7×7 basis element pairs. -/
theorem d_leibniz_proof (ia ib : NilpotentDGBasis) :
  d (mul (basis ia) (basis ib)) = mul (d (basis ia)) (basis ib) + (((-1 : ℂ) ^ (NilpotentDGBasis.degree ia)) • (mul (basis ia) (d (basis ib)))) := by
  -- In RNT-LIGHT, all differentials vanish: d(all generators) = 0
  have h_d_one : d (basis .one) = zero := d_basis_one_is_zero
  have h_d_eps1 : d (basis .eps1) = zero := d_basis_eps1
  have h_d_eps2 : d (basis .eps2) = zero := d_basis_eps2
  have h_d_theta : d (basis .theta) = zero := d_basis_theta
  have h_d_eps1eps2 : d (basis .eps1eps2) = zero := d_basis_eps1eps2_proved
  have h_d_eps1theta : d (basis .eps1theta) = zero := d_basis_eps1theta_proved
  have h_d_eps2theta : d (basis .eps2theta) = zero := d_basis_eps2theta_proved

  -- Exhaustive case analysis over all 64 = 7×7 basis element pairs
  cases ia <;> cases ib
  -- ia = .one (degree 0)
  case one.one =>
    rw [one_mul_any, h_d_one, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_zero, one_smul, mul_zero_BasisAlgebra]
    exact (add_zero_BasisAlgebra zero).symm
  case one.eps1 =>
    rw [one_mul_any, h_d_one, h_d_eps1, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_zero, one_smul, mul_zero_BasisAlgebra]
    exact (add_zero_BasisAlgebra zero).symm
  case one.eps2 =>
    rw [one_mul_any, h_d_one, h_d_eps2, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_zero, one_smul, mul_zero_BasisAlgebra]
    exact (add_zero_BasisAlgebra zero).symm
  case one.theta =>
    rw [one_mul_any, h_d_one, h_d_theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_zero, one_smul]
    have h_one_mul_zero : mul (basis .one) zero = zero := mul_zero_BasisAlgebra (basis .one)
    rw [h_one_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case one.eps1eps2 =>
    rw [one_mul_any, h_d_one, h_d_eps1eps2, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_zero, one_smul, mul_zero_BasisAlgebra]
    exact (add_zero_BasisAlgebra zero).symm
  case one.eps1theta =>
    rw [one_mul_any, h_d_one, h_d_eps1theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_zero, one_smul, mul_zero_BasisAlgebra]
    exact (add_zero_BasisAlgebra zero).symm
  case one.eps2theta =>
    rw [one_mul_any, h_d_one, h_d_eps2theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_zero, one_smul, mul_zero_BasisAlgebra]
    exact (add_zero_BasisAlgebra zero).symm

  -- ia = .eps1 (degree 1)
  case eps1.one =>
    rw [mul_one_any, h_d_eps1, h_d_one, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_one, neg_one_smul, mul_zero_BasisAlgebra, neg_zero_eq_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps1.eps1 =>
    -- ε₁² = 0 (nilpotency)
    simp only [eps1_sq_is_zero, d_zero_is_zero, h_d_eps1, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, mul_zero_BasisAlgebra]
    norm_num
    rw [← zero_eq_ring_zero] at *
  case eps1.eps2 =>
    -- ε₁ε₂ is a basis element, d(ε₁ε₂) = 0
    rw [← basis_eps1eps2_is_prod, h_d_eps1eps2, h_d_eps1, h_d_eps2, zero_mul_BasisAlgebra, mul_zero_BasisAlgebra]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps1.theta =>
    -- ε₁θ is a basis element, d(ε₁θ) = 0
    rw [← basis_eps1theta_is_prod, h_d_eps1theta, h_d_eps1, h_d_theta, zero_mul_BasisAlgebra]
    have h_eps1_mul_zero : mul (basis .eps1) zero = zero := mul_zero_BasisAlgebra (basis .eps1)
    rw [h_eps1_mul_zero]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps1.eps1eps2 =>
    -- ε₁(ε₁ε₂) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1) (basis .eps1eps2) = zero := eps1_mul_eps1eps2_is_zero
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1, h_d_eps1eps2, zero_mul_BasisAlgebra, mul_zero_BasisAlgebra]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps1.eps1theta =>
    -- ε₁(ε₁θ) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1) (basis .eps1theta) = zero := mul_eps1_eps1theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1, h_d_eps1theta, zero_mul_BasisAlgebra, mul_zero_BasisAlgebra]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps1.eps2theta =>
    -- ε₁(ε₂θ) = 0 (follows from ε₁ε₂θ = 0)
    have h_eps1_eps2theta : mul (basis .eps1) (basis .eps2theta) = zero := mul_eps1_eps2theta
    rw [h_eps1_eps2theta, d_zero_is_zero, h_d_eps1, h_d_eps2theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_one, neg_one_smul, mul_zero_BasisAlgebra, neg_zero_eq_zero]
    exact (add_zero_BasisAlgebra zero).symm

  -- ia = .eps2 (degree 1)
  case eps2.one =>
    rw [mul_one_any, h_d_eps2, h_d_one, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_one, neg_one_smul, mul_zero_BasisAlgebra, neg_zero_eq_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps2.eps1 =>
    -- ε₂ε₁ = ε₁ε₂ (commutativity)
    rw [← eps1_eps2_commutes, ← basis_eps1eps2_is_prod, h_d_eps1eps2, h_d_eps2, h_d_eps1, zero_mul_BasisAlgebra, mul_zero_BasisAlgebra]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps2.eps2 =>
    -- ε₂² = 0 (nilpotency)
    simp only [eps2_sq_is_zero, d_zero_is_zero, h_d_eps2, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, mul_zero_BasisAlgebra]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps2.theta =>
    -- ε₂θ is a basis element, d(ε₂θ) = 0
    have h_eps2_theta : mul (basis .eps2) (basis .theta) = basis .eps2theta := basis_eps2theta_is_prod.symm
    rw [h_eps2_theta, h_d_eps2theta, h_d_eps2, h_d_theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_one, neg_one_smul]
    have h_eps2_mul_zero : mul (basis .eps2) zero = zero := mul_zero_BasisAlgebra (basis .eps2)
    rw [h_eps2_mul_zero]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps2.eps1eps2 =>
    -- ε₂(ε₁ε₂) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps2) (basis .eps1eps2) = zero := mul_eps2_eps1eps2_is_zero
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps2, h_d_eps1eps2, zero_mul_BasisAlgebra, mul_zero_BasisAlgebra]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps2.eps1theta =>
    -- ε₂(ε₁θ) = 0 (follows from ε₁ε₂θ = 0)
    have h_mul_is_zero : mul (basis .eps2) (basis .eps1theta) = zero := by
      ext b; cases b <;> simp [mul, basis, zero]
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps2, h_d_eps1theta, zero_mul_BasisAlgebra, mul_zero_BasisAlgebra]
    simp [smul_zero]
    exact zero_eq_ring_zero.symm
  case eps2.eps2theta =>
    -- ε₂(ε₂θ) = 0 (higher-order nilpotency)
    have h_eps2_eps2theta : mul (basis .eps2) (basis .eps2theta) = zero := mul_eps2_eps2theta
    rw [h_eps2_eps2theta, d_zero_is_zero, h_d_eps2, h_d_eps2theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_one, neg_one_smul, mul_zero_BasisAlgebra, neg_zero_eq_zero]
    exact (add_zero_BasisAlgebra zero).symm

  -- ia = .theta (degree 2)
  case theta.one =>
    rw [mul_one_any, h_d_theta, h_d_one, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_zero_mul_one : zero.mul (basis .one) = zero := zero_mul_BasisAlgebra (basis .one)
    rw [h_zero_mul_one]
    exact (add_zero_BasisAlgebra zero).symm
  case theta.eps1 =>
    -- θε₁ = ε₁θ (commutativity)
    rw [← eps1_theta_commutes, ← basis_eps1theta_is_prod, h_d_eps1theta, h_d_theta, h_d_eps1, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_zero_mul_eps1 : zero.mul (basis .eps1) = zero := zero_mul_BasisAlgebra (basis .eps1)
    rw [h_zero_mul_eps1]
    exact (add_zero_BasisAlgebra zero).symm
  case theta.eps2 =>
    -- θε₂ = ε₂θ (commutativity)
    have h_theta_eps2_eq_eps2_theta : mul (basis .theta) (basis .eps2) = mul (basis .eps2) (basis .theta) := eps2_theta_commutes.symm
    rw [h_theta_eps2_eq_eps2_theta, ← basis_eps2theta_is_prod, h_d_eps2theta, h_d_theta, h_d_eps2, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_zero_mul_eps2 : zero.mul (basis .eps2) = zero := zero_mul_BasisAlgebra (basis .eps2)
    rw [h_zero_mul_eps2]
    exact (add_zero_BasisAlgebra zero).symm
  case theta.theta =>
    -- θ² = 0 (nilpotency)
    simp only [theta_sq_is_zero, d_zero_is_zero, h_d_theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_theta_mul_zero : mul (basis .theta) zero = zero := mul_zero_BasisAlgebra (basis .theta)
    rw [h_theta_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case theta.eps1eps2 =>
    -- θ(ε₁ε₂) = 0 (follows from ε₁ε₂θ = 0)
    have h_mul_is_zero : mul (basis .theta) (basis .eps1eps2) = zero := mul_theta_eps1eps2
    rw [h_mul_is_zero, d_zero_is_zero, h_d_theta, h_d_eps1eps2, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_zero_mul_eps1eps2 : zero.mul (basis .eps1eps2) = zero := zero_mul_BasisAlgebra (basis .eps1eps2)
    rw [h_zero_mul_eps1eps2]
    exact (add_zero_BasisAlgebra zero).symm
  case theta.eps1theta =>
    -- θ(ε₁θ) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .theta) (basis .eps1theta) = zero := mul_theta_eps1theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_theta, h_d_eps1theta, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_zero_mul_eps1theta : zero.mul (basis .eps1theta) = zero := zero_mul_BasisAlgebra (basis .eps1theta)
    rw [h_zero_mul_eps1theta]
    simp [pow_three, neg_one_smul, smul_zero]
    exact zero_eq_ring_zero.symm
  case theta.eps2theta =>
    -- θ(ε₂θ) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .theta) (basis .eps2theta) = zero := mul_theta_eps2theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_theta, h_d_eps2theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_theta_mul_zero : mul (basis .theta) zero = zero := mul_zero_BasisAlgebra (basis .theta)
    rw [h_theta_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm

  -- ia = .eps1eps2 (degree 2)
  case eps1eps2.one =>
    rw [mul_one_any, h_d_eps1eps2, h_d_one, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_eps1eps2_mul_zero : mul (basis .eps1eps2) zero = zero := mul_zero_BasisAlgebra (basis .eps1eps2)
    rw [h_eps1eps2_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps1eps2.eps1 =>
    -- (ε₁ε₂)ε₁ = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1eps2) (basis .eps1) = zero := eps1eps2_mul_eps1_is_zero
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1eps2, h_d_eps1, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_eps1eps2_mul_zero : mul (basis .eps1eps2) zero = zero := mul_zero_BasisAlgebra (basis .eps1eps2)
    rw [h_eps1eps2_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps1eps2.eps2 =>
    -- (ε₁ε₂)ε₂ = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1eps2) (basis .eps2) = zero := mul_eps1eps2_eps2_is_zero
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1eps2, h_d_eps2, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_eps1eps2_mul_zero : mul (basis .eps1eps2) zero = zero := mul_zero_BasisAlgebra (basis .eps1eps2)
    rw [h_eps1eps2_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps1eps2.theta =>
    -- (ε₁ε₂)θ = 0 (critical relation from RNT-LIGHT Section 1.1)
    have h_mul_is_zero : mul (basis .eps1eps2) (basis .theta) = zero := by
      ext b; cases b <;> simp [mul, basis, zero]
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1eps2, h_d_theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_eps1eps2_mul_zero : mul (basis .eps1eps2) zero = zero := mul_zero_BasisAlgebra (basis .eps1eps2)
    rw [h_eps1eps2_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps1eps2.eps1eps2 =>
    -- (ε₁ε₂)² = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1eps2) (basis .eps1eps2) = zero := mul_eps1eps2_eps1eps2_is_zero
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1eps2, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_eps1eps2_mul_zero : mul (basis .eps1eps2) zero = zero := mul_zero_BasisAlgebra (basis .eps1eps2)
    rw [h_eps1eps2_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps1eps2.eps1theta =>
    -- (ε₁ε₂)(ε₁θ) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1eps2) (basis .eps1theta) = zero := mul_eps1eps2_eps1theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1eps2, h_d_eps1theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul]
    have h_eps1eps2_mul_zero : mul (basis .eps1eps2) zero = zero := mul_zero_BasisAlgebra (basis .eps1eps2)
    rw [h_eps1eps2_mul_zero]
    exact (add_zero_BasisAlgebra zero).symm
  case eps1eps2.eps2theta =>
    -- (ε₁ε₂)(ε₂θ) = 0 (higher-order nilpotency)
    have h_eps1eps2_eps2theta : mul (basis .eps1eps2) (basis .eps2theta) = zero := mul_eps1eps2_eps2theta
    rw [h_eps1eps2_eps2theta, d_zero_is_zero, h_d_eps1eps2, h_d_eps2theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, neg_one_pow_two_eq_one, one_smul, mul_zero_BasisAlgebra]
    exact (add_zero_BasisAlgebra zero).symm

  -- ia = .eps1theta (degree 3)
  case eps1theta.one =>
    rw [mul_one_any, h_d_eps1theta, h_d_one, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three, mul_zero_BasisAlgebra]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps1theta.eps1 =>
    -- (ε₁θ)ε₁ = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1theta) (basis .eps1) = zero := mul_eps1theta_eps1
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1theta, h_d_eps1, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three, mul_zero_BasisAlgebra]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps1theta.eps2 =>
    -- (ε₁θ)ε₂ = 0 (follows from ε₁ε₂θ = 0)
    have h_eps1theta_eps2 : mul (basis .eps1theta) (basis .eps2) = zero := by
      ext b; cases b <;> simp [mul, basis, zero]
    rw [h_eps1theta_eps2, d_zero_is_zero, h_d_eps1theta, h_d_eps2, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three, mul_zero_BasisAlgebra]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps1theta.theta =>
    -- (ε₁θ)θ = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1theta) (basis .theta) = zero := mul_eps1theta_theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1theta, h_d_theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three]
    have h_eps1theta_mul_zero : mul (basis .eps1theta) zero = zero := mul_zero_BasisAlgebra (basis .eps1theta)
    rw [h_eps1theta_mul_zero]
    simp [pow_three, neg_one_smul, smul_zero]
    exact zero_eq_ring_zero.symm
  case eps1theta.eps1eps2 =>
    -- (ε₁θ)(ε₁ε₂) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1theta) (basis .eps1eps2) = zero := mul_eps1theta_eps1eps2
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1theta, h_d_eps1eps2, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three, mul_zero_BasisAlgebra]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps1theta.eps1theta =>
    -- (ε₁θ)² = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1theta) (basis .eps1theta) = zero := mul_eps1theta_eps1theta_is_zero
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three, mul_zero_BasisAlgebra]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps1theta.eps2theta =>
    -- (ε₁θ)(ε₂θ) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps1theta) (basis .eps2theta) = zero := mul_eps1theta_eps2theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps1theta, h_d_eps2theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three]
    have h_eps1theta_mul_zero : mul (basis .eps1theta) zero = zero := mul_zero_BasisAlgebra (basis .eps1theta)
    rw [h_eps1theta_mul_zero]
    simp [pow_three, neg_one_smul, smul_zero]
    exact zero_eq_ring_zero.symm

  -- ia = .eps2theta (degree 3)
  case eps2theta.one =>
    rw [mul_one_any, h_d_eps2theta, h_d_one, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three]
    have h_eps2theta_mul_zero : mul (basis .eps2theta) zero = zero := mul_zero_BasisAlgebra (basis .eps2theta)
    rw [h_eps2theta_mul_zero]
    simp [pow_three, neg_one_smul, smul_zero]
    exact zero_eq_ring_zero.symm
  case eps2theta.eps1 =>
    -- (ε₂θ)ε₁ = 0 (follows from ε₁ε₂θ = 0)
    have h_eps2theta_eps1 : mul (basis .eps2theta) (basis .eps1) = zero := by
      ext b; cases b <;> simp [mul, basis, zero]
    rw [h_eps2theta_eps1, d_zero_is_zero, h_d_eps2theta, h_d_eps1, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, pow_three]
    simp only [pow_three, neg_one_smul, smul_zero, zero_mul_BasisAlgebra]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps2theta.eps2 =>
    -- (ε₂θ)ε₂ = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps2theta) (basis .eps2) = zero := mul_eps2theta_eps2
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps2theta, h_d_eps2, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, pow_three]
    have h_zero_mul_eps2 : zero.mul (basis .eps2) = zero := zero_mul_BasisAlgebra (basis .eps2)
    rw [h_zero_mul_eps2]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps2theta.theta =>
    -- (ε₂θ)θ = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps2theta) (basis .theta) = zero := mul_eps2theta_theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps2theta, h_d_theta, zero_mul_BasisAlgebra, NilpotentDGBasis.degree, pow_three]
    have h_eps2theta_mul_zero : mul (basis .eps2theta) zero = zero := mul_zero_BasisAlgebra (basis .eps2theta)
    rw [h_eps2theta_mul_zero]
    simp [pow_three, neg_one_smul, smul_zero]
    exact zero_eq_ring_zero.symm
  case eps2theta.eps1eps2 =>
    -- (ε₂θ)(ε₁ε₂) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps2theta) (basis .eps1eps2) = zero := mul_eps2theta_eps1eps2
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps2theta, h_d_eps1eps2, mul_zero_BasisAlgebra, NilpotentDGBasis.degree, pow_three]
    have h_zero_mul_eps1eps2 : zero.mul (basis .eps1eps2) = zero := zero_mul_BasisAlgebra (basis .eps1eps2)
    rw [h_zero_mul_eps1eps2]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps2theta.eps1theta =>
    -- (ε₂θ)(ε₁θ) = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps2theta) (basis .eps1theta) = zero := mul_eps2theta_eps1theta
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps2theta, h_d_eps1theta, NilpotentDGBasis.degree, pow_three]
    have h_zero_mul_eps1theta : zero.mul (basis .eps1theta) = zero := zero_mul_BasisAlgebra (basis .eps1theta)
    have h_eps2theta_zero : mul (basis .eps2theta) zero = zero := mul_zero_BasisAlgebra (basis .eps2theta)
    rw [h_zero_mul_eps1theta, h_eps2theta_zero]
    norm_num
    exact zero_eq_ring_zero.symm
  case eps2theta.eps2theta =>
    -- (ε₂θ)² = 0 (higher-order nilpotency)
    have h_mul_is_zero : mul (basis .eps2theta) (basis .eps2theta) = zero := mul_eps2theta_eps2theta_is_zero
    rw [h_mul_is_zero, d_zero_is_zero, h_d_eps2theta, NilpotentDGBasis.degree, pow_three]
    have h_zero_mul_eps2theta : zero.mul (basis .eps2theta) = zero := zero_mul_BasisAlgebra (basis .eps2theta)
    have h_eps2theta_zero : mul (basis .eps2theta) zero = zero := mul_zero_BasisAlgebra (basis .eps2theta)
    rw [h_zero_mul_eps2theta, h_eps2theta_zero]
    norm_num
    exact zero_eq_ring_zero.symm

/-- d² = 0 property of the differential (RNT-LIGHT Theorem T3).
In RNT-LIGHT with trivial differential d ≡ 0, this reduces to d(d(a)) = d(0) = 0. -/
theorem d_squared (a : BasisAlgebra) : d (d a) = zero := by
  -- With trivial differential, d(a) = 0 for all a
  have h_d_a_zero : d a = zero := by
    ext c
    simp only [d, zero]
  -- Therefore d(d(a)) = d(0) = 0
  rw [h_d_a_zero, d_zero_is_zero]

/-- Critical relation ε₁ε₂θ = 0 from RNT-LIGHT Section 1.1.
This relation characterizes the socle structure and ensures dim Soc(A_ε) = 3. -/
theorem eps1eps2_theta_is_zero : mul (mul (basis .eps1) (basis .eps2)) (basis .theta) = zero := by
  -- Transform (ε₁ε₂)θ using basis element representation
  rw [← basis_eps1eps2_is_prod]
  -- Now prove (ε₁ε₂)·θ = 0
  ext b
  cases b <;> simp [mul, basis, zero]

/-- Products of degree 4 vanish.
Since max degree in A_ε is 3, all products of total degree 4 must be zero.
This theorem exhaustively verifies all such combinations. -/
theorem degree_4_is_zero (ia ib ic : NilpotentDGBasis)
    (h : ia.degree + ib.degree + ic.degree = 4) :
    mul (mul (basis ia) (basis ib)) (basis ic) = zero := by
  -- Max degree in A_ε is 3, so degree 4 products vanish
  -- Possible degree combinations: (0,1,3), (0,2,2), (1,1,2), (1,2,1), (2,1,1), etc.

  cases ia <;> cases ib <;> cases ic <;> simp [NilpotentDGBasis.degree] at h

  -- Most cases lead to arithmetic contradictions (eliminated by omega)
  try omega

  -- Handle only valid degree-4 cases

  -- Cases (0,1,3): 1 · ε₁/ε₂ · ε₁θ/ε₂θ
  case one.eps1.eps1theta => rw [one_mul_any]; exact mul_eps1_eps1theta
  case one.eps1.eps2theta => rw [one_mul_any]; exact mul_eps1_eps2theta
  case one.eps2.eps1theta => rw [one_mul_any]; exact mul_eps2_eps1theta
  case one.eps2.eps2theta => rw [one_mul_any]; exact mul_eps2_eps2theta

  -- Cases (0,2,2): 1 · θ/ε₁ε₂ · θ/ε₁ε₂
  case one.theta.theta => rw [one_mul_any]; exact theta_sq_is_zero
  case one.theta.eps1eps2 => rw [one_mul_any]; exact mul_theta_eps1eps2
  case one.eps1eps2.theta => rw [one_mul_any]; ext b; cases b <;> simp [mul, basis, zero]
  case one.eps1eps2.eps1eps2 => rw [one_mul_any]; exact mul_eps1eps2_eps1eps2_is_zero

  -- Cases (0,3,1): 1 · ε₁θ/ε₂θ · ε₁/ε₂
  case one.eps1theta.eps1 => rw [one_mul_any]; exact mul_eps1theta_eps1
  case one.eps1theta.eps2 => rw [one_mul_any]; ext b; cases b <;> simp [mul, basis, zero]
  case one.eps2theta.eps1 => rw [one_mul_any]; ext b; cases b <;> simp [mul, basis, zero]
  case one.eps2theta.eps2 => rw [one_mul_any]; exact mul_eps2theta_eps2

  -- Cases (1,0,3): ε₁/ε₂ · 1 · ε₁θ/ε₂θ
  case eps1.one.eps1theta => rw [mul_one_any]; exact mul_eps1_eps1theta
  case eps1.one.eps2theta => rw [mul_one_any]; exact mul_eps1_eps2theta
  case eps2.one.eps1theta => rw [mul_one_any]; exact mul_eps2_eps1theta
  case eps2.one.eps2theta => rw [mul_one_any]; exact mul_eps2_eps2theta

  -- Cases (1,1,2): ε₁/ε₂ · ε₁/ε₂ · θ/ε₁ε₂
  case eps1.eps1.theta => rw [eps1_sq_is_zero, zero_mul_BasisAlgebra]
  case eps1.eps1.eps1eps2 => rw [eps1_sq_is_zero, zero_mul_BasisAlgebra]
  case eps1.eps2.theta => rw [← basis_eps1eps2_is_prod]; ext b; cases b <;> simp [mul, basis, zero]
  case eps1.eps2.eps1eps2 => rw [← basis_eps1eps2_is_prod]; exact mul_eps1eps2_eps1eps2_is_zero
  case eps2.eps1.theta =>
    -- ε₂ε₁ = ε₁ε₂, so (ε₂ε₁)θ = (ε₁ε₂)θ = 0 (critical relation)
    have h_comm : mul (basis .eps2) (basis .eps1) = mul (basis .eps1) (basis .eps2) := eps1_eps2_commutes.symm
    rw [h_comm, ← basis_eps1eps2_is_prod]; ext b; cases b <;> simp [mul, basis, zero]
  case eps2.eps1.eps1eps2 =>
    have h_comm : mul (basis .eps2) (basis .eps1) = mul (basis .eps1) (basis .eps2) := eps1_eps2_commutes.symm
    rw [h_comm, ← basis_eps1eps2_is_prod]; exact mul_eps1eps2_eps1eps2_is_zero
  case eps2.eps2.theta => rw [eps2_sq_is_zero, zero_mul_BasisAlgebra]
  case eps2.eps2.eps1eps2 => rw [eps2_sq_is_zero, zero_mul_BasisAlgebra]

  -- Cases (1,2,1): ε₁/ε₂ · θ/ε₁ε₂ · ε₁/ε₂
  case eps1.theta.eps1 => rw [← basis_eps1theta_is_prod]; exact mul_eps1theta_eps1
  case eps1.theta.eps2 => rw [← basis_eps1theta_is_prod]; ext b; cases b <;> simp [mul, basis, zero]
  case eps1.eps1eps2.eps1 => rw [eps1_mul_eps1eps2_is_zero, zero_mul_BasisAlgebra]
  case eps1.eps1eps2.eps2 => rw [eps1_mul_eps1eps2_is_zero, zero_mul_BasisAlgebra]
  case eps2.theta.eps1 => rw [← basis_eps2theta_is_prod]; ext b; cases b <;> simp [mul, basis, zero]
  case eps2.theta.eps2 => rw [← basis_eps2theta_is_prod]; exact mul_eps2theta_eps2
  case eps2.eps1eps2.eps1 => rw [mul_eps2_eps1eps2_is_zero, zero_mul_BasisAlgebra]
  case eps2.eps1eps2.eps2 => rw [mul_eps2_eps1eps2_is_zero, zero_mul_BasisAlgebra]

  -- Cases (1,3,0): ε₁/ε₂ · ε₁θ/ε₂θ · 1
  case eps1.eps1theta.one =>
    -- Use associativity: (ε₁ · ε₁θ) · 1 = ε₁ · (ε₁θ · 1) = ε₁ · ε₁θ = 0
    rw [mul_assoc_BasisAlgebra]
    have h_eps1theta_one : mul (basis .eps1theta) (basis .one) = basis .eps1theta := mul_one_BasisAlgebra _
    rw [h_eps1theta_one]; exact mul_eps1_eps1theta
  case eps1.eps2theta.one =>
    rw [mul_assoc_BasisAlgebra]
    have h_eps2theta_one : mul (basis .eps2theta) (basis .one) = basis .eps2theta := mul_one_BasisAlgebra _
    rw [h_eps2theta_one]; exact mul_eps1_eps2theta
  case eps2.eps1theta.one =>
    rw [mul_assoc_BasisAlgebra]
    have h_eps1theta_one : mul (basis .eps1theta) (basis .one) = basis .eps1theta := mul_one_BasisAlgebra _
    rw [h_eps1theta_one]; exact mul_eps2_eps1theta
  case eps2.eps2theta.one =>
    rw [mul_assoc_BasisAlgebra]
    have h_eps2theta_one : mul (basis .eps2theta) (basis .one) = basis .eps2theta := mul_one_BasisAlgebra _
    rw [h_eps2theta_one]; exact mul_eps2_eps2theta

  -- Cases (2,0,2): θ/ε₁ε₂ · 1 · θ/ε₁ε₂
  case theta.one.theta => rw [mul_one_any]; exact theta_sq_is_zero
  case theta.one.eps1eps2 => rw [mul_one_any]; exact mul_theta_eps1eps2
  case eps1eps2.one.theta => rw [mul_one_any]; ext b; cases b <;> simp [mul, basis, zero]
  case eps1eps2.one.eps1eps2 => rw [mul_one_any]; exact mul_eps1eps2_eps1eps2_is_zero

  -- Cases (2,1,1): θ/ε₁ε₂ · ε₁/ε₂ · ε₁/ε₂
  case theta.eps1.eps1 => rw [← eps1_theta_commutes, ← basis_eps1theta_is_prod]; exact mul_eps1theta_eps1
  case theta.eps1.eps2 => rw [← eps1_theta_commutes, ← basis_eps1theta_is_prod]; ext b; cases b <;> simp [mul, basis, zero]
  case theta.eps2.eps1 => rw [← eps2_theta_commutes, ← basis_eps2theta_is_prod]; ext b; cases b <;> simp [mul, basis, zero]
  case theta.eps2.eps2 => rw [← eps2_theta_commutes, ← basis_eps2theta_is_prod]; exact mul_eps2theta_eps2
  case eps1eps2.eps1.eps1 => rw [eps1eps2_mul_eps1_is_zero, zero_mul_BasisAlgebra]
  case eps1eps2.eps1.eps2 => rw [eps1eps2_mul_eps1_is_zero, zero_mul_BasisAlgebra]
  case eps1eps2.eps2.eps1 => rw [mul_eps1eps2_eps2_is_zero, zero_mul_BasisAlgebra]
  case eps1eps2.eps2.eps2 => rw [mul_eps1eps2_eps2_is_zero, zero_mul_BasisAlgebra]

  -- Cases (2,2,0): θ/ε₁ε₂ · θ/ε₁ε₂ · 1
  case theta.theta.one => rw [theta_sq_is_zero, zero_mul_BasisAlgebra]
  case theta.eps1eps2.one => rw [mul_theta_eps1eps2, zero_mul_BasisAlgebra]
  case eps1eps2.theta.one => ext b; cases b <;> simp [mul, basis, zero, zero_mul_BasisAlgebra]
  case eps1eps2.eps1eps2.one => rw [mul_eps1eps2_eps1eps2_is_zero, zero_mul_BasisAlgebra]

  -- Cases (3,0,1): ε₁θ/ε₂θ · 1 · ε₁/ε₂
  case eps1theta.one.eps1 => rw [mul_one_any]; exact mul_eps1theta_eps1
  case eps1theta.one.eps2 => rw [mul_one_any]; ext b; cases b <;> simp [mul, basis, zero]
  case eps2theta.one.eps1 => rw [mul_one_any]; ext b; cases b <;> simp [mul, basis, zero]
  case eps2theta.one.eps2 => rw [mul_one_any]; exact mul_eps2theta_eps2

  -- Cases (3,1,0): ε₁θ/ε₂θ · ε₁/ε₂ · 1
  case eps1theta.eps1.one =>
    rw [mul_assoc_BasisAlgebra]
    have h_eps1_one : mul (basis .eps1) (basis .one) = basis .eps1 := mul_one_BasisAlgebra _
    rw [h_eps1_one]; exact mul_eps1theta_eps1
  case eps1theta.eps2.one =>
    rw [mul_assoc_BasisAlgebra]
    have h_eps2_one : mul (basis .eps2) (basis .one) = basis .eps2 := mul_one_BasisAlgebra _
    rw [h_eps2_one]; ext b; cases b <;> simp [mul, basis, zero]
  case eps2theta.eps1.one =>
    rw [mul_assoc_BasisAlgebra]
    have h_eps1_one : mul (basis .eps1) (basis .one) = basis .eps1 := mul_one_BasisAlgebra _
    rw [h_eps1_one]; ext b; cases b <;> simp [mul, basis, zero]
  case eps2theta.eps2.one =>
    rw [mul_assoc_BasisAlgebra]
    have h_eps2_one : mul (basis .eps2) (basis .one) = basis .eps2 := mul_one_BasisAlgebra _
    rw [h_eps2_one]; exact mul_eps2theta_eps2

/-- Summary of all nilpotent relations in A_ε (RNT-LIGHT Theorem T2 and Section 1.1).
This collects the key identities: ε₁² = ε₂² = θ² = 0 and ε₁ε₂θ = 0. -/
theorem nilpotent_relations_check :
  mul (basis .eps1) (basis .eps1) = zero ∧
  mul (basis .eps2) (basis .eps2) = zero ∧
  mul (basis .theta) (basis .theta) = zero ∧
  mul (mul (basis .eps1) (basis .eps2)) (basis .theta) = zero := by
  exact ⟨eps1_sq_is_zero, eps2_sq_is_zero, theta_sq_is_zero, eps1eps2_theta_is_zero⟩

/-! ### Socle structure
The socle section has been deferred pending proper ideal formalization.
See RNT-LIGHT Theorem 1.7: dim Soc(A_ε) = 3 follows from ε₁ε₂θ = 0.
-/

end RNT.Algebra.BasisAlgebra
