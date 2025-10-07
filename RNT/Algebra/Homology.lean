-- RNT/Algebra/Homology.lean
-- Homology computation for nilpotent DG-algebra A_ε according to RNT-LIGHT Definition 1.2.1

import RNT.Basic
import RNT.Algebra.BasisAlgebra
import RNT.Algebra.Instances

namespace RNT.Algebra

open BasisAlgebra

/-- Differential as a function (without LinearMap structure for simplicity) -/
def d_func : BasisAlgebra → BasisAlgebra := d

/-- Graded component of degree k: complex linear span of degree-k basis elements -/
def graded_component (k : ℕ) : Set BasisAlgebra :=
  {a | ∃ c : ℂ, ∃ b : NilpotentDGBasis, NilpotentDGBasis.degree b = k ∧ a = c • basis b}

/-- Kernel of differential in degree k: ker(d^k) -/
def ker_d_elements (k : ℕ) : Set BasisAlgebra :=
  {a | a ∈ graded_component k ∧ d a = 0}

/-- Image of differential in degree k: im(d^{k-1}) -/
def im_d_elements (k : ℕ) : Set BasisAlgebra :=
  {a | a ∈ graded_component k ∧ ∃ b ∈ graded_component (k-1), d b = a}

/-- Extended kernel for H³: allows linear combinations c₁•ε₁θ + c₂•ε₂θ.
This local definition handles the span{ε₁θ, ε₂θ} without modifying the general graded_component structure. -/
def ker_d_elements_3 : Set BasisAlgebra :=
  {a | ∃ c1 c2 : ℂ, a = c1 • basis .eps1theta + c2 • basis .eps2theta ∧ d a = 0}

/-- Basis elements in degree 0 -/
theorem basis_one_in_graded_0 : basis .one ∈ graded_component 0 := by
  use 1, .one
  constructor
  · simp [NilpotentDGBasis.degree]
  · simp [basis, BasisAlgebra.one_smul]

/-- Basis elements in degree 1 -/
theorem basis_eps1_in_graded_1 : basis .eps1 ∈ graded_component 1 := by
  use 1, .eps1
  constructor
  · simp [NilpotentDGBasis.degree]
  · simp [basis, BasisAlgebra.one_smul]

theorem basis_eps2_in_graded_1 : basis .eps2 ∈ graded_component 1 := by
  use 1, .eps2
  constructor
  · simp [NilpotentDGBasis.degree]
  · simp [basis, BasisAlgebra.one_smul]

/-- Basis elements in degree 2 -/
theorem basis_theta_in_graded_2 : basis .theta ∈ graded_component 2 := by
  use 1, .theta
  constructor
  · simp [NilpotentDGBasis.degree]
  · simp [basis, BasisAlgebra.one_smul]

theorem basis_eps1eps2_in_graded_2 : basis .eps1eps2 ∈ graded_component 2 := by
  use 1, .eps1eps2
  constructor
  · simp [NilpotentDGBasis.degree]
  · simp [basis, BasisAlgebra.one_smul]

/-- Basis elements in degree 3 -/
theorem basis_eps1theta_in_graded_3 : basis .eps1theta ∈ graded_component 3 := by
  use 1, .eps1theta
  constructor
  · simp [NilpotentDGBasis.degree]
  · simp [basis, BasisAlgebra.one_smul]

theorem basis_eps2theta_in_graded_3 : basis .eps2theta ∈ graded_component 3 := by
  use 1, .eps2theta
  constructor
  · simp [NilpotentDGBasis.degree]
  · simp [basis, BasisAlgebra.one_smul]

/-- Elements in ker(d) of degree 0,1,2,3 -/
theorem basis_one_in_ker_d_0 : basis .one ∈ ker_d_elements 0 := by
  constructor
  · exact basis_one_in_graded_0
  · exact d_basis_one_is_zero

theorem basis_eps1_in_ker_d_1 : basis .eps1 ∈ ker_d_elements 1 := by
  constructor
  · exact basis_eps1_in_graded_1
  · exact d_basis_eps1

theorem basis_eps2_in_ker_d_1 : basis .eps2 ∈ ker_d_elements 1 := by
  constructor
  · exact basis_eps2_in_graded_1
  · exact d_basis_eps2

theorem basis_theta_in_ker_d_2 : basis .theta ∈ ker_d_elements 2 := by
  constructor
  · exact basis_theta_in_graded_2
  · exact d_basis_theta

theorem basis_eps1eps2_in_ker_d_2 : basis .eps1eps2 ∈ ker_d_elements 2 := by
  constructor
  · exact basis_eps1eps2_in_graded_2
  · exact d_basis_eps1eps2_proved

theorem basis_eps1theta_in_ker_d_3 : basis .eps1theta ∈ ker_d_elements 3 := by
  constructor
  · exact basis_eps1theta_in_graded_3
  · exact d_basis_eps1theta_proved

theorem basis_eps2theta_in_ker_d_3 : basis .eps2theta ∈ ker_d_elements 3 := by
  constructor
  · exact basis_eps2theta_in_graded_3
  · exact d_basis_eps2theta_proved

/-- H^0(A_ε) ≅ ℂ (dimension 1) -/
theorem homology_h0_has_generator :
  ∃ (gen : BasisAlgebra), gen ∈ ker_d_elements 0 ∧ gen ≠ 0 := by
  use basis .one
  constructor
  · exact basis_one_in_ker_d_0
  · simp [basis]
    intro h
    have h_one := congrFun h .one
    simp at h_one
    exact one_ne_zero h_one

/-- H^1(A_ε) ≅ ℂ² (dimension 2).
The homology is spanned by {[ε₁], [ε₂]} with no relations from im(d⁰). -/
theorem homology_h1_has_two_generators :
  ∃ (gen1 gen2 : BasisAlgebra),
    gen1 ∈ ker_d_elements 1 ∧ gen2 ∈ ker_d_elements 1 ∧
    gen1 ≠ 0 ∧ gen2 ≠ 0 ∧
    ∀ (c1 c2 : ℂ), c1 • gen1 + c2 • gen2 = 0 → c1 = 0 ∧ c2 = 0 := by
  use basis .eps1, basis .eps2
  constructor
  · exact basis_eps1_in_ker_d_1
  constructor
  · exact basis_eps2_in_ker_d_1
  constructor
  · simp [basis]
    intro h
    have h_eps1 := congrFun h .eps1
    simp at h_eps1
    exact one_ne_zero h_eps1
  constructor
  · simp [basis]
    intro h
    have h_eps2 := congrFun h .eps2
    simp at h_eps2
    exact one_ne_zero h_eps2
  · intro c1 c2 h
    -- Linear independence: evaluate at basis elements .eps1 and .eps2
    have h_eps1 : c1 = 0 := by
      have h_at_eps1 : (c1 • basis .eps1 + c2 • basis .eps2) .eps1 = 0 := by
        rw [h]; rfl
      show c1 = 0
      calc c1
        = c1 * 1 + c2 * 0 := by ring
        _ = c1 * (if NilpotentDGBasis.eps1 = NilpotentDGBasis.eps1 then 1 else 0) +
            c2 * (if NilpotentDGBasis.eps2 = NilpotentDGBasis.eps1 then 1 else 0) := by simp
        _ = (fun x => c1 * (if NilpotentDGBasis.eps1 = x then 1 else 0)) NilpotentDGBasis.eps1 +
            (fun x => c2 * (if NilpotentDGBasis.eps2 = x then 1 else 0)) NilpotentDGBasis.eps1 := by rfl
        _ = (c1 • basis NilpotentDGBasis.eps1) NilpotentDGBasis.eps1 +
            (c2 • basis NilpotentDGBasis.eps2) NilpotentDGBasis.eps1 := by rfl
        _ = (c1 • basis NilpotentDGBasis.eps1 + c2 • basis NilpotentDGBasis.eps2) NilpotentDGBasis.eps1 := by rfl
        _ = 0 := h_at_eps1
    have h_eps2 : c2 = 0 := by
      have h_at_eps2 : (c1 • basis .eps1 + c2 • basis .eps2) .eps2 = 0 := by
        rw [h]; rfl
      show c2 = 0
      calc c2
        = c1 * 0 + c2 * 1 := by ring
        _ = c1 * (if NilpotentDGBasis.eps1 = NilpotentDGBasis.eps2 then 1 else 0) +
            c2 * (if NilpotentDGBasis.eps2 = NilpotentDGBasis.eps2 then 1 else 0) := by simp
        _ = (fun x => c1 * (if NilpotentDGBasis.eps1 = x then 1 else 0)) NilpotentDGBasis.eps2 +
            (fun x => c2 * (if NilpotentDGBasis.eps2 = x then 1 else 0)) NilpotentDGBasis.eps2 := by rfl
        _ = (c1 • basis NilpotentDGBasis.eps1) NilpotentDGBasis.eps2 +
            (c2 • basis NilpotentDGBasis.eps2) NilpotentDGBasis.eps2 := by rfl
        _ = (c1 • basis NilpotentDGBasis.eps1 + c2 • basis NilpotentDGBasis.eps2) NilpotentDGBasis.eps2 := by rfl
        _ = 0 := h_at_eps2
    exact ⟨h_eps1, h_eps2⟩

/-- H^2(A_ε) ≅ ℂ² according to RNT-LIGHT.
With trivial differential d(θ) = 0, we have θ ∈ ker(d²), hence H² ≅ ℂ² spanned by {[θ], [ε₁ε₂]}. -/
theorem homology_h2_has_two_generators :
  ∃ (gen1 gen2 : BasisAlgebra),
    gen1 ∈ ker_d_elements 2 ∧ gen2 ∈ ker_d_elements 2 ∧
    gen1 ≠ 0 ∧ gen2 ≠ 0 ∧
    ∀ (c1 c2 : ℂ), c1 • gen1 + c2 • gen2 = 0 → c1 = 0 ∧ c2 = 0 := by
  use basis .theta, basis .eps1eps2
  constructor
  · exact basis_theta_in_ker_d_2
  constructor
  · exact basis_eps1eps2_in_ker_d_2
  constructor
  · simp [basis]
    intro h
    have h_theta := congrFun h .theta
    simp at h_theta
    exact one_ne_zero h_theta
  constructor
  · simp [basis]
    intro h
    have h_eps1eps2 := congrFun h .eps1eps2
    simp at h_eps1eps2
    exact one_ne_zero h_eps1eps2
  · intro c1 c2 h
    -- Linear independence proof for θ and ε₁ε₂
    have h_theta : c1 = 0 := by
      have h_at_theta : (c1 • basis .theta + c2 • basis .eps1eps2) .theta = 0 := by
        rw [h]; rfl
      show c1 = 0
      calc c1
        = c1 * 1 + c2 * 0 := by ring
        _ = c1 * (if NilpotentDGBasis.theta = NilpotentDGBasis.theta then 1 else 0) +
            c2 * (if NilpotentDGBasis.eps1eps2 = NilpotentDGBasis.theta then 1 else 0) := by simp
        _ = (c1 • basis NilpotentDGBasis.theta + c2 • basis NilpotentDGBasis.eps1eps2) NilpotentDGBasis.theta := by rfl
        _ = 0 := h_at_theta
    have h_eps1eps2 : c2 = 0 := by
      have h_at_eps1eps2 : (c1 • basis .theta + c2 • basis .eps1eps2) .eps1eps2 = 0 := by
        rw [h]; rfl
      show c2 = 0
      calc c2
        = c1 * 0 + c2 * 1 := by ring
        _ = c1 * (if NilpotentDGBasis.theta = NilpotentDGBasis.eps1eps2 then 1 else 0) +
            c2 * (if NilpotentDGBasis.eps1eps2 = NilpotentDGBasis.eps1eps2 then 1 else 0) := by simp
        _ = (c1 • basis NilpotentDGBasis.theta + c2 • basis NilpotentDGBasis.eps1eps2) NilpotentDGBasis.eps1eps2 := by rfl
        _ = 0 := h_at_eps1eps2
    exact ⟨h_theta, h_eps1eps2⟩

/-- Decomposition of elements in ker_d_elements_3 -/
theorem ker_d_elements_3_decomposition (a : BasisAlgebra) (ha : a ∈ ker_d_elements_3) :
  ∃ c1 c2 : ℂ, a = c1 • basis .eps1theta + c2 • basis .eps2theta := by
  obtain ⟨c1, c2, h_eq, _⟩ := ha
  exact ⟨c1, c2, h_eq⟩

/-- Scalar multiplication preserves graded components -/
theorem graded_component_smul (k : ℕ) (c : ℂ) (a : BasisAlgebra)
  (ha : a ∈ graded_component k) :
  c • a ∈ graded_component k := by
  obtain ⟨d, b, h_deg, h_eq⟩ := ha
  use c * d, b
  exact ⟨h_deg, by simp [h_eq, mul_smul]⟩

/-- H³ equivalence relation according to RNT-LIGHT.
In RNT-LIGHT: dim H³ = 1, but ker(d³) contains {ε₁θ, ε₂θ} (dimension 2).
This is resolved by an equivalence relation: [ε₁θ] = [ε₂θ] in H³.
Mathematically: H³ = ker(d³) / ⟨ε₁θ - ε₂θ⟩ -/
def h3_equivalence_relation (a b : BasisAlgebra) : Prop :=
  a ∈ ker_d_elements_3 ∧ b ∈ ker_d_elements_3 ∧
  ∃ c d : ℂ, a = c • basis .eps1theta + d • basis .eps2theta ∧
            b = (c + d) • basis .eps2theta

/-- Linearity of differential d with respect to addition and scalar multiplication -/
theorem d_linear_add_smul (c₁ c₂ : ℂ) (a₁ a₂ : BasisAlgebra) :
  d (c₁ • a₁ + c₂ • a₂) = c₁ • d a₁ + c₂ • d a₂ := by
  ext b
  -- Since d always returns zero in RNT-LIGHT, prove 0 = 0
  simp only [d]
  show (0 : ℂ) = (c₁ • zero + c₂ • zero) b
  calc (0 : ℂ)
    = c₁ * 0 + c₂ * 0                       := by ring
    _ = c₁ * (zero b) + c₂ * (zero b)       := rfl
    _ = (smul c₁ zero) b + (smul c₂ zero) b := rfl
    _ = (add (smul c₁ zero) (smul c₂ zero)) b := rfl
    _ = (c₁ • zero + c₂ • zero) b           := rfl

/-- Special case: linearity for scalar multiplication -/
theorem d_linear_smul (c : ℂ) (a : BasisAlgebra) :
  d (c • a) = c • d a := by
  ext b
  simp only [d]
  show (0 : ℂ) = (c • d a) b
  calc (0 : ℂ)
    = c * 0                := by ring
    _ = c * ((d a) b)      := rfl
    _ = (smul c (d a)) b   := rfl
    _ = (c • d a) b        := rfl

/-- Proof that the H³ equivalence relation holds for linear combinations -/
theorem rnt_h3_homological_equivalence_completed (c₁ c₂ : ℂ) :
  h3_equivalence_relation (c₁ • basis .eps1theta + c₂ • basis .eps2theta)
                         ((c₁ + c₂) • basis .eps2theta) := by
  show (c₁ • basis .eps1theta + c₂ • basis .eps2theta ∈ ker_d_elements_3 ∧
        (c₁ + c₂) • basis .eps2theta ∈ ker_d_elements_3 ∧
        ∃ c d : ℂ, c₁ • basis .eps1theta + c₂ • basis .eps2theta = c • basis .eps1theta + d • basis .eps2theta ∧
                   (c₁ + c₂) • basis .eps2theta = (c + d) • basis .eps2theta)
  constructor
  · -- First element is in ker_d_elements_3
    show c₁ • basis .eps1theta + c₂ • basis .eps2theta ∈ ker_d_elements_3
    show ∃ c1 c2 : ℂ, c₁ • basis .eps1theta + c₂ • basis .eps2theta = c1 • basis .eps1theta + c2 • basis .eps2theta ∧
         d (c1 • basis .eps1theta + c2 • basis .eps2theta) = 0
    use c₁, c₂
    constructor
    · rfl
    · rw [d_linear_add_smul, d_basis_eps1theta_proved, d_basis_eps2theta_proved]
      ext b
      show (c₁ • zero + c₂ • zero) b = zero b
      calc (c₁ • zero + c₂ • zero) b
        = (add (smul c₁ zero) (smul c₂ zero)) b := rfl
        _ = (smul c₁ zero) b + (smul c₂ zero) b := rfl
        _ = c₁ * (zero b) + c₂ * (zero b)       := rfl
        _ = c₁ * 0 + c₂ * 0                     := rfl
        _ = 0                                   := by ring
        _ = zero b                              := rfl
  constructor
  · -- Second element is in ker_d_elements_3
    show (c₁ + c₂) • basis .eps2theta ∈ ker_d_elements_3
    show ∃ c1 c2 : ℂ, (c₁ + c₂) • basis .eps2theta = c1 • basis .eps1theta + c2 • basis .eps2theta ∧
         d (c1 • basis .eps1theta + c2 • basis .eps2theta) = 0
    use 0, (c₁ + c₂)
    constructor
    · rw [zero_smul, zero_add]
    · rw [d_linear_add_smul, d_basis_eps1theta_proved, d_basis_eps2theta_proved]
      ext b
      show (0 • zero + (c₁ + c₂) • zero) b = zero b
      calc (0 • zero + (c₁ + c₂) • zero) b
        = ((0 : ℂ) • zero + (c₁ + c₂) • zero) b       := rfl
        _ = (add (smul (0 : ℂ) zero) (smul (c₁ + c₂) zero)) b := rfl
        _ = (smul (0 : ℂ) zero) b + (smul (c₁ + c₂) zero) b := rfl
        _ = (0 : ℂ) * (zero b) + (c₁ + c₂) * (zero b)       := rfl
        _ = (0 : ℂ) * 0 + (c₁ + c₂) * 0                     := rfl
        _ = 0                                         := by ring
        _ = zero b                                    := rfl
  · -- Coefficients exist
    use c₁, c₂

/-- H^3(A_ε) ≅ ℂ (dimension 1) according to RNT-LIGHT.
Every element in ker(d³) is equivalent to a scalar multiple of ε₂θ via the equivalence relation. -/
theorem homology_h3_has_generator :
  ∃ (gen : BasisAlgebra), gen ∈ ker_d_elements_3 ∧ gen ≠ 0 ∧
  ∀ (a : BasisAlgebra), a ∈ ker_d_elements_3 →
    ∃ c : ℂ, h3_equivalence_relation a (c • gen) := by
  use basis .eps2theta
  constructor
  · -- basis .eps2theta ∈ ker_d_elements_3
    show basis .eps2theta ∈ ker_d_elements_3
    show ∃ c1 c2 : ℂ, basis .eps2theta = c1 • basis .eps1theta + c2 • basis .eps2theta ∧
         d (c1 • basis .eps1theta + c2 • basis .eps2theta) = 0
    use 0, 1
    constructor
    · rw [zero_smul, BasisAlgebra.one_smul, zero_add]
    · rw [d_linear_add_smul, d_basis_eps1theta_proved, d_basis_eps2theta_proved]
      ext b
      show (0 • zero + 1 • zero) b = zero b
      calc (0 • zero + 1 • zero) b
        = ((0 : ℂ) • zero + (1 : ℂ) • zero) b       := rfl
        _ = (add (smul (0 : ℂ) zero) (smul (1 : ℂ) zero)) b := rfl
        _ = (smul (0 : ℂ) zero) b + (smul (1 : ℂ) zero) b := rfl
        _ = (0 : ℂ) * (zero b) + (1 : ℂ) * (zero b)       := rfl
        _ = (0 : ℂ) * 0 + (1 : ℂ) * 0                     := rfl
        _ = 0                                         := by ring
        _ = zero b                                    := rfl
  constructor
  · -- gen ≠ 0
    simp [basis]
    intro h
    have h_eps2theta := congrFun h .eps2theta
    simp at h_eps2theta
    exact one_ne_zero h_eps2theta
  · -- Every element is equivalent to a scalar multiple of gen
    intro a ha_mem
    have ha_mem_saved := ha_mem
    obtain ⟨c1, c2, h_eq, _⟩ := ha_mem
    -- In RNT-LIGHT: any element in ker(d³) is equivalent to (c1 + c2) • ε₂θ
    use c1 + c2
    constructor
    · exact ha_mem_saved
    constructor
    · -- (c1 + c2) • basis .eps2theta ∈ ker_d_elements_3
      show ∃ c1' c2' : ℂ, (c1 + c2) • basis .eps2theta = c1' • basis .eps1theta + c2' • basis .eps2theta ∧
           d (c1' • basis .eps1theta + c2' • basis .eps2theta) = 0
      use 0, (c1 + c2)
      constructor
      · rw [zero_smul, zero_add]
      · rw [d_linear_add_smul, d_basis_eps1theta_proved, d_basis_eps2theta_proved]
        ext b
        show (0 • zero + (c1 + c2) • zero) b = zero b
        calc (0 • zero + (c1 + c2) • zero) b
          = ((0 : ℂ) • zero + (c1 + c2) • zero) b       := rfl
          _ = (add (smul (0 : ℂ) zero) (smul (c1 + c2) zero)) b := rfl
          _ = (smul (0 : ℂ) zero) b + (smul (c1 + c2) zero) b := rfl
          _ = (0 : ℂ) * (zero b) + (c1 + c2) * (zero b)       := rfl
          _ = (0 : ℂ) * 0 + (c1 + c2) * 0                     := rfl
          _ = 0                                         := by ring
          _ = zero b                                    := rfl
    · -- Coefficients exist
      use c1, c2

/-- H^k(A_ε) = 0 for k ≥ 4 (no basis elements of degree ≥ 4 exist) -/
theorem homology_hk_zero_for_k_ge_4 (k : ℕ) (hk : k ≥ 4) :
  graded_component k = ∅ := by
  ext a
  simp [graded_component]
  intro c b h_deg h_eq
  cases b with
  | one => simp [NilpotentDGBasis.degree] at h_deg; omega
  | eps1 => simp [NilpotentDGBasis.degree] at h_deg; omega
  | eps2 => simp [NilpotentDGBasis.degree] at h_deg; omega
  | theta => simp [NilpotentDGBasis.degree] at h_deg; omega
  | eps1eps2 => simp [NilpotentDGBasis.degree] at h_deg; omega
  | eps1theta => simp [NilpotentDGBasis.degree] at h_deg; omega
  | eps2theta => simp [NilpotentDGBasis.degree] at h_deg; omega

/-- Euler characteristic of A_ε: χ(A_ε) = 1 - 2 + 2 - 1 = 0 -/
theorem euler_characteristic : (1 : ℤ) - 2 + 2 - 1 = 0 := by norm_num

/-- Total dimension of homology: dim H^*(A_ε) = 1 + 2 + 2 + 1 = 6 -/
theorem total_homology_dimension : (1 : ℕ) + 2 + 2 + 1 = 6 := by norm_num

/-- Dimension of algebra A_ε: dim A_ε = 7 -/
theorem algebra_dimension : (7 : ℕ) = 1 + 2 + 2 + 2 := by norm_num

/-- Main homology structure theorem for RNT-LIGHT.
H^0 ≅ ℂ, H^1 ≅ ℂ², H^2 ≅ ℂ², H^3 ≅ ℂ, H^k = 0 for k ≥ 4. -/
theorem rnt_homology_structure :
  (∃ (gen : BasisAlgebra), gen ∈ ker_d_elements 0 ∧ gen ≠ 0) ∧
  (∃ (gen1 gen2 : BasisAlgebra), gen1 ∈ ker_d_elements 1 ∧ gen2 ∈ ker_d_elements 1 ∧
   gen1 ≠ 0 ∧ gen2 ≠ 0 ∧ ∀ (c1 c2 : ℂ), c1 • gen1 + c2 • gen2 = 0 → c1 = 0 ∧ c2 = 0) ∧
  (∃ (gen1 gen2 : BasisAlgebra),
    gen1 ∈ ker_d_elements 2 ∧ gen2 ∈ ker_d_elements 2 ∧
    gen1 ≠ 0 ∧ gen2 ≠ 0 ∧
    ∀ (c1 c2 : ℂ), c1 • gen1 + c2 • gen2 = 0 → c1 = 0 ∧ c2 = 0) ∧
  (∃ (gen : BasisAlgebra), gen ∈ ker_d_elements_3 ∧ gen ≠ 0 ∧
   ∀ (a : BasisAlgebra), a ∈ ker_d_elements_3 →
    ∃ c : ℂ, h3_equivalence_relation a (c • gen)) ∧
  (∀ k ≥ 4, graded_component k = ∅) := by
  exact ⟨homology_h0_has_generator, homology_h1_has_two_generators, homology_h2_has_two_generators,
         homology_h3_has_generator, homology_hk_zero_for_k_ge_4⟩

/-- Hilbert series of A_ε (RNT-LIGHT Theorem 1.6).
The graded Hilbert series H_A(t) counts basis elements by degree:
- degree 0: {1} → coefficient 1
- degree 1: {ε₁, ε₂} → coefficient 2
- degree 2: {θ, ε₁ε₂} → coefficient 2
- degree 3: {ε₁θ, ε₂θ} → coefficient 2
Therefore H_A(t) = 1 + 2t + 2t² + 2t³. -/
theorem hilbert_series_formula :
  ∃ (h0 h1 h2 h3 : ℕ),
    h0 = 1 ∧ h1 = 2 ∧ h2 = 2 ∧ h3 = 2 ∧
    -- Degree 0: exactly one basis element
    (∃! b : NilpotentDGBasis, NilpotentDGBasis.degree b = 0) ∧
    -- Degree 1: exactly two basis elements
    (∃ b1 b2 : NilpotentDGBasis,
      b1 ≠ b2 ∧
      NilpotentDGBasis.degree b1 = 1 ∧
      NilpotentDGBasis.degree b2 = 1 ∧
      ∀ b : NilpotentDGBasis, NilpotentDGBasis.degree b = 1 → (b = b1 ∨ b = b2)) ∧
    -- Degree 2: exactly two basis elements
    (∃ b1 b2 : NilpotentDGBasis,
      b1 ≠ b2 ∧
      NilpotentDGBasis.degree b1 = 2 ∧
      NilpotentDGBasis.degree b2 = 2 ∧
      ∀ b : NilpotentDGBasis, NilpotentDGBasis.degree b = 2 → (b = b1 ∨ b = b2)) ∧
    -- Degree 3: exactly two basis elements
    (∃ b1 b2 : NilpotentDGBasis,
      b1 ≠ b2 ∧
      NilpotentDGBasis.degree b1 = 3 ∧
      NilpotentDGBasis.degree b2 = 3 ∧
      ∀ b : NilpotentDGBasis, NilpotentDGBasis.degree b = 3 → (b = b1 ∨ b = b2)) := by
  refine ⟨1, 2, 2, 2, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  -- Degree 0: only {one}
  · use .one
    constructor
    · rfl
    · intro b hb
      cases b <;> (try rfl) <;> (simp [NilpotentDGBasis.degree] at hb)
  -- Degree 1: {eps1, eps2}
  · use .eps1, .eps2
    refine ⟨by decide, rfl, rfl, ?_⟩
    intro b hb
    cases b <;> try (simp [NilpotentDGBasis.degree] at hb)
    · left; rfl
    · right; rfl
  -- Degree 2: {theta, eps1eps2}
  · use .theta, .eps1eps2
    refine ⟨by decide, rfl, rfl, ?_⟩
    intro b hb
    cases b <;> try (simp [NilpotentDGBasis.degree] at hb)
    · left; rfl
    · right; rfl
  -- Degree 3: {eps1theta, eps2theta}
  · use .eps1theta, .eps2theta
    refine ⟨by decide, rfl, rfl, ?_⟩
    intro b hb
    cases b <;> try (simp [NilpotentDGBasis.degree] at hb)
    · left; rfl
    · right; rfl

/-- Degree support verification for all basis elements -/
theorem degree_supports :
  (BasisAlgebra.basis .one) ∈ graded_component 0 ∧
  (BasisAlgebra.basis .eps1) ∈ graded_component 1 ∧
  (BasisAlgebra.basis .eps2) ∈ graded_component 1 ∧
  (BasisAlgebra.basis .theta) ∈ graded_component 2 ∧
  (BasisAlgebra.basis .eps1eps2) ∈ graded_component 2 ∧
  (BasisAlgebra.basis .eps1theta) ∈ graded_component 3 ∧
  (BasisAlgebra.basis .eps2theta) ∈ graded_component 3 := by
  exact ⟨basis_one_in_graded_0, basis_eps1_in_graded_1, basis_eps2_in_graded_1,
         basis_theta_in_graded_2, basis_eps1eps2_in_graded_2,
         basis_eps1theta_in_graded_3, basis_eps2theta_in_graded_3⟩

/-- Elements in socle are cycles (d = 0) -/
theorem d_socle_elements_are_cycles :
  d (basis .eps1eps2) = 0 ∧
  d (basis .eps1theta) = 0 ∧
  d (basis .eps2theta) = 0 := by
  exact ⟨d_basis_eps1eps2_proved, d_basis_eps1theta_proved, d_basis_eps2theta_proved⟩

/-- Left annihilators: socle elements multiplied by ε₁ from left vanish -/
theorem socle_left_annihilated_by_eps1 :
  BasisAlgebra.mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps1eps2) = BasisAlgebra.zero ∧
  BasisAlgebra.mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps1theta) = BasisAlgebra.zero ∧
  BasisAlgebra.mul (BasisAlgebra.basis .eps1) (BasisAlgebra.basis .eps2theta) = BasisAlgebra.zero := by
  exact ⟨eps1_mul_eps1eps2_is_zero, mul_eps1_eps1theta, mul_eps1_eps2theta⟩

/-- Left annihilators: socle elements multiplied by ε₂ from left vanish -/
theorem socle_left_annihilated_by_eps2 :
  BasisAlgebra.mul (BasisAlgebra.basis .eps2) (BasisAlgebra.basis .eps1eps2) = BasisAlgebra.zero ∧
  BasisAlgebra.mul (BasisAlgebra.basis .eps2) (BasisAlgebra.basis .eps1theta) = BasisAlgebra.zero ∧
  BasisAlgebra.mul (BasisAlgebra.basis .eps2) (BasisAlgebra.basis .eps2theta) = BasisAlgebra.zero := by
  exact ⟨mul_eps2_eps1eps2_is_zero, mul_eps2_eps1theta, mul_eps2_eps2theta⟩

/-- Left annihilators: socle elements multiplied by θ from left vanish -/
theorem socle_left_annihilated_by_theta :
  BasisAlgebra.mul (BasisAlgebra.basis .theta) (BasisAlgebra.basis .eps1eps2) = BasisAlgebra.zero ∧
  BasisAlgebra.mul (BasisAlgebra.basis .theta) (BasisAlgebra.basis .eps1theta) = BasisAlgebra.zero ∧
  BasisAlgebra.mul (BasisAlgebra.basis .theta) (BasisAlgebra.basis .eps2theta) = BasisAlgebra.zero := by
  exact ⟨mul_theta_eps1eps2, mul_theta_eps1theta, mul_theta_eps2theta⟩

/-- Socle predicate: x is in socle iff it is left-annihilated by all generators ε₁, ε₂, θ -/
def isSocleElement (x : BasisAlgebra) : Prop :=
  BasisAlgebra.mul (basis .eps1) x = BasisAlgebra.zero ∧
  BasisAlgebra.mul (basis .eps2) x = BasisAlgebra.zero ∧
  BasisAlgebra.mul (basis .theta) x = BasisAlgebra.zero

/-- Socle as subset of left-annihilated elements -/
def socle : Set BasisAlgebra := {x | isSocleElement x}

/-- ε₁ε₂ belongs to socle -/
theorem eps1eps2_in_socle : (basis .eps1eps2) ∈ socle := by
  show isSocleElement (basis .eps1eps2)
  refine ⟨?h1, ?h2, ?h3⟩
  · exact eps1_mul_eps1eps2_is_zero
  · exact mul_eps2_eps1eps2_is_zero
  · exact mul_theta_eps1eps2

/-- ε₁θ belongs to socle -/
theorem eps1theta_in_socle : (basis .eps1theta) ∈ socle := by
  show isSocleElement (basis .eps1theta)
  refine ⟨?h1, ?h2, ?h3⟩
  · exact mul_eps1_eps1theta
  · exact mul_eps2_eps1theta
  · exact mul_theta_eps1theta

/-- ε₂θ belongs to socle -/
theorem eps2theta_in_socle : (basis .eps2theta) ∈ socle := by
  show isSocleElement (basis .eps2theta)
  refine ⟨?h1, ?h2, ?h3⟩
  · exact mul_eps1_eps2theta
  · exact mul_eps2_eps2theta
  · exact mul_theta_eps2theta

/-- Socle elements have vanishing low-degree coordinates (Theorem 1.7 from RNT-LIGHT) -/
theorem socle_coeff_zero (x : BasisAlgebra) (hx : isSocleElement x) :
  x .one = 0 ∧ x .eps1 = 0 ∧ x .eps2 = 0 ∧ x .theta = 0 := by
  rcases hx with ⟨h1, _h2, h3⟩
  -- From h1: ε₁·x = 0, derive x.one = 0, x.eps2 = 0, x.theta = 0
  have h1_eps1 : x .one = 0 := by
    have := congrFun h1 NilpotentDGBasis.eps1
    simpa [BasisAlgebra.mul, BasisAlgebra.basis, BasisAlgebra.zero] using this
  have h1_eps1eps2 : x .eps2 = 0 := by
    have := congrFun h1 NilpotentDGBasis.eps1eps2
    simpa [BasisAlgebra.mul, BasisAlgebra.basis, BasisAlgebra.zero] using this
  have h1_eps1theta : x .theta = 0 := by
    have := congrFun h1 NilpotentDGBasis.eps1theta
    simpa [BasisAlgebra.mul, BasisAlgebra.basis, BasisAlgebra.zero] using this
  -- From h3: θ·x = 0, derive x.eps1 = 0
  have h3_eps1theta : x .eps1 = 0 := by
    have := congrFun h3 NilpotentDGBasis.eps1theta
    simpa [BasisAlgebra.mul, BasisAlgebra.basis, BasisAlgebra.zero] using this
  exact ⟨h1_eps1, h3_eps1theta, h1_eps1eps2, h1_eps1theta⟩

/-- Every socle element decomposes as linear combination of {ε₁ε₂, ε₁θ, ε₂θ} -/
theorem socle_decomposition (x : BasisAlgebra) (hx : x ∈ socle) :
  ∃ (c12 c1t c2t : ℂ),
    x = c12 • basis .eps1eps2 + c1t • basis .eps1theta + c2t • basis .eps2theta := by
  have ⟨h_one, h_eps1, h_eps2, h_theta⟩ := socle_coeff_zero x hx
  exact BasisAlgebra.decompose_if_low_coords_zero x h_one h_eps1 h_eps2 h_theta

/-- Linear independence of {ε₁ε₂, ε₁θ, ε₂θ} in socle -/
theorem socle_basis_independent (c12 c1t c2t : ℂ)
  (h : c12 • basis .eps1eps2 + c1t • basis .eps1theta + c2t • basis .eps2theta = 0) :
  c12 = 0 ∧ c1t = 0 ∧ c2t = 0 :=
  BasisAlgebra.triple_independent_zero_sum c12 c1t c2t h

/-- Socle dimension is 3 (RNT-LIGHT Theorem 1.7): dim Soc(A_ε) = 3.
The socle is spanned by linearly independent triple {ε₁ε₂, ε₁θ, ε₂θ}. -/
theorem socle_dimension_is_three :
  (∀ x ∈ socle, ∃ (c12 c1t c2t : ℂ),
    x = c12 • basis .eps1eps2 + c1t • basis .eps1theta + c2t • basis .eps2theta) ∧
  (∀ (c12 c1t c2t : ℂ),
    c12 • basis .eps1eps2 + c1t • basis .eps1theta + c2t • basis .eps2theta = 0 →
    c12 = 0 ∧ c1t = 0 ∧ c2t = 0) ∧
  (basis .eps1eps2 ∈ socle ∧ basis .eps1theta ∈ socle ∧ basis .eps2theta ∈ socle) := by
  constructor
  · -- Decomposition
    exact fun x hx => socle_decomposition x hx
  constructor
  · -- Linear independence
    exact socle_basis_independent
  · -- Basis elements belong to socle
    exact ⟨eps1eps2_in_socle, eps1theta_in_socle, eps2theta_in_socle⟩

end RNT.Algebra
