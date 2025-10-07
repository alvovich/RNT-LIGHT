-- RNT/Algebra/BasisAlgebra.lean
-- Concrete realization of nilpotent DG-algebra via basis functions

import RNT.Basic
import RNT.Algebra.Generators
import RNT.Algebra.Structure

namespace RNT.Algebra

/-- Concrete realization of nilpotent DG-algebra as functions NilpotentDGBasis → ℂ.
This functional representation makes the 7-dimensional vector space structure explicit. -/
def BasisAlgebra := NilpotentDGBasis → ℂ

namespace BasisAlgebra

/-- Addition of algebra elements -/
def add (a b : BasisAlgebra) : BasisAlgebra := fun b' => a b' + b b'

/-- Scalar multiplication -/
def smul (c : ℂ) (a : BasisAlgebra) : BasisAlgebra := fun b => c * a b

/-- Negation -/
def neg (a : BasisAlgebra) : BasisAlgebra := fun b => -a b

/-- Zero element -/
def zero : BasisAlgebra := fun _ => 0

/-- Unit element -/
def one : BasisAlgebra := fun b => if b = NilpotentDGBasis.one then 1 else 0

/-- Multiplication via explicit multiplication table encoding nilpotency ε₁ε₂θ = 0 -/
def mul (a b : BasisAlgebra) : BasisAlgebra := fun c =>
  match c with
  | .one => a .one * b .one
  | .eps1 => a .one * b .eps1 + a .eps1 * b .one
  | .eps2 => a .one * b .eps2 + a .eps2 * b .one
  | .theta => a .one * b .theta + a .theta * b .one
  | .eps1eps2 => a .one * b .eps1eps2 + a .eps1eps2 * b .one +
                 a .eps1 * b .eps2 + a .eps2 * b .eps1
  | .eps1theta => a .one * b .eps1theta + a .eps1theta * b .one +
                  a .eps1 * b .theta + a .theta * b .eps1
  | .eps2theta => a .one * b .eps2theta + a .eps2theta * b .one +
                  a .eps2 * b .theta + a .theta * b .eps2

/-- Differential on algebra elements. In RNT-LIGHT, d ≡ 0 (trivial differential). -/
def d (_ : BasisAlgebra) : BasisAlgebra := fun c =>
  match c with
  | _ => 0

/-- Grade of an element: maximum degree of nonzero basis components -/
noncomputable def grade (a : BasisAlgebra) : ℕ :=
  if a .eps1theta ≠ 0 ∨ a .eps2theta ≠ 0 then 3
  else if a .theta ≠ 0 ∨ a .eps1eps2 ≠ 0 then 2
  else if a .eps1 ≠ 0 ∨ a .eps2 ≠ 0 then 1
  else if a .one ≠ 0 then 0
  else 0

/-- Standard basis element -/
def basis (b : NilpotentDGBasis) : BasisAlgebra :=
  fun c => if b = c then 1 else 0

@[ext] theorem ext {f g : BasisAlgebra} : (∀ b, f b = g b) → f = g :=
  funext

def natsmul_rec : ℕ → BasisAlgebra → BasisAlgebra
  | 0, _ => zero
  | n + 1, a => add a (natsmul_rec n a)

instance instAddBasisAlgebra : Add BasisAlgebra := ⟨add⟩
instance instMulBasisAlgebra : Mul BasisAlgebra := ⟨mul⟩
instance instZeroBasisAlgebra : Zero BasisAlgebra := ⟨zero⟩
instance instOneBasisAlgebra : One BasisAlgebra := ⟨one⟩
instance instNegBasisAlgebra : Neg BasisAlgebra := ⟨neg⟩
instance instSMulBasisAlgebra : SMul ℂ BasisAlgebra := ⟨smul⟩

theorem one_mul_BasisAlgebra (a : BasisAlgebra) : mul one a = a := by
  funext c_val; cases c_val <;> simp [mul, one, add_zero, zero_add, one_mul, zero_mul]

theorem mul_one_BasisAlgebra (a : BasisAlgebra) : mul a one = a := by
  funext c_val; cases c_val <;> simp [mul, one, add_zero, zero_add, one_mul, zero_mul]

theorem mul_assoc_BasisAlgebra (a b c_el : BasisAlgebra) : mul (mul a b) c_el = mul a (mul b c_el) := by
  ext x
  cases x <;> dsimp [BasisAlgebra.mul] <;> ring

instance instMonoidBasisAlgebra : Monoid BasisAlgebra where
  mul := mul
  mul_assoc := mul_assoc_BasisAlgebra
  one := one
  one_mul := one_mul_BasisAlgebra
  mul_one := mul_one_BasisAlgebra

theorem left_distrib_BasisAlgebra (a b c_el : BasisAlgebra) : mul a (add b c_el) = add (mul a b) (mul a c_el) := by
  ext x
  cases x <;> (dsimp only [BasisAlgebra.mul, BasisAlgebra.add]; ring)

theorem right_distrib_BasisAlgebra (a b c_el : BasisAlgebra) : mul (add a b) c_el = add (mul a c_el) (mul b c_el) := by
  ext x
  cases x <;> (dsimp only [BasisAlgebra.mul, BasisAlgebra.add]; ring)

theorem add_assoc_BasisAlgebra (a b c : BasisAlgebra) : a + b + c = a + (b + c) := by
  apply ext; intro x
  dsimp [add]
  exact add_assoc (a x) (b x) (c x)

theorem zero_add_BasisAlgebra (a : BasisAlgebra) : 0 + a = a := by
  apply ext; intro x
  dsimp [add, zero]
  exact zero_add (a x)

theorem add_zero_BasisAlgebra (a : BasisAlgebra) : a + 0 = a := by
  apply ext; intro x
  dsimp [add, zero]
  exact add_zero (a x)

theorem add_comm_BasisAlgebra (a b : BasisAlgebra) : a + b = b + a := by
  apply ext; intro x
  dsimp [add]
  exact add_comm (a x) (b x)

instance instAddCommMonoidBasisAlgebra : AddCommMonoid BasisAlgebra where
  add := add
  add_assoc := add_assoc_BasisAlgebra
  zero := zero
  zero_add := zero_add_BasisAlgebra
  add_zero := add_zero_BasisAlgebra
  add_comm := add_comm_BasisAlgebra
  nsmul := natsmul_rec
  nsmul_zero := by { intro x; simp only [natsmul_rec]; rfl }
  nsmul_succ := by
    intro n x; simp only [natsmul_rec];
    exact add_comm_BasisAlgebra x (natsmul_rec n x)

instance : Sub BasisAlgebra where sub a b := add a (BasisAlgebra.neg b)

def basis_zsmul : ℤ → BasisAlgebra → BasisAlgebra
  | .ofNat k, a => natsmul_rec k a
  | .negSucc k, a => BasisAlgebra.neg (natsmul_rec (k+1) a)

instance : SMul ℤ BasisAlgebra where
  smul := basis_zsmul

instance : SubNegMonoid BasisAlgebra where
  toAddMonoid := instAddCommMonoidBasisAlgebra.toAddMonoid
  toNeg := inferInstance
  toSub := inferInstance
  sub_eq_add_neg := by
    intro a b; apply ext; intro x;
    rfl
  zsmul := basis_zsmul
  zsmul_zero' := by
    intro a; apply ext; intro x; simp only [basis_zsmul, Int.ofNat_zero, natsmul_rec, zero]; rfl
  zsmul_succ' := by
    intro n x
    apply ext
    intro b
    unfold basis_zsmul
    simp only [basis_zsmul, natsmul_rec, BasisAlgebra.add]
    exact add_comm (x b) ((natsmul_rec n x) b)
  zsmul_neg' := by
    intro n x
    unfold basis_zsmul
    rfl

instance : AddGroup BasisAlgebra where
  toSubNegMonoid := inferInstance
  neg_add_cancel := by
    intro a
    apply ext
    intro b
    dsimp only [BasisAlgebra.add, BasisAlgebra.neg, BasisAlgebra.zero]
    exact neg_add_cancel (a b)

/-- Nilpotency relations: ε₁² = ε₂² = θ² = 0 (Theorem T2 from RNT-LIGHT) -/
theorem eps1_sq_is_zero : mul (basis .eps1) (basis .eps1) = zero := by
  funext b
  cases b <;> simp [mul, basis, zero]

theorem eps2_sq_is_zero : mul (basis .eps2) (basis .eps2) = zero := by
  funext b
  cases b <;> simp [mul, basis, zero]

theorem theta_sq_is_zero : mul (basis .theta) (basis .theta) = zero := by
  funext b
  cases b <;> simp [mul, basis, zero]

/-- Commutation relations (Theorem T2 from RNT-LIGHT) -/
theorem eps1_eps2_commutes : mul (basis .eps1) (basis .eps2) = mul (basis .eps2) (basis .eps1) := by
  funext b
  cases b <;> simp [mul, basis]

theorem eps1_theta_commutes : mul (basis .eps1) (basis .theta) = mul (basis .theta) (basis .eps1) := by
  funext b
  cases b <;> simp [mul, basis]

theorem eps2_theta_commutes : mul (basis .eps2) (basis .theta) = mul (basis .theta) (basis .eps2) := by
  funext b
  cases b <;> simp [mul, basis]

/-- Basis products -/
theorem basis_eps1eps2_is_prod : basis .eps1eps2 = mul (basis .eps1) (basis .eps2) := by
  funext b
  cases b <;> simp [mul, basis]

theorem basis_eps1theta_is_prod : basis .eps1theta = mul (basis .eps1) (basis .theta) := by
  funext b
  cases b <;> simp [mul, basis]

theorem basis_eps2theta_is_prod : basis .eps2theta = mul (basis .eps2) (basis .theta) := by
  funext b
  cases b <;> simp [mul, basis]

/-- Critical relation ε₁ε₂θ = 0 from RNT-LIGHT Section 1.1 -/
theorem eps1eps2theta_is_zero : mul (mul (basis .eps1) (basis .eps2)) (basis .theta) = zero := by
  ext b
  rw [← basis_eps1eps2_is_prod]
  cases b <;> simp [mul, basis, zero]

/-- Differential of basis elements (d ≡ 0 in RNT-LIGHT) -/
theorem d_basis_one_is_zero : d (basis .one) = zero := by
  ext c_val
  unfold d zero
  rfl

theorem d_basis_eps1 : d (basis .eps1) = zero := by
  ext c_val
  unfold d zero
  rfl

theorem d_basis_eps2 : d (basis .eps2) = zero := by
  ext c_val
  unfold d zero
  rfl

theorem d_basis_theta : d (basis .theta) = zero := by
  ext c_val
  unfold d zero
  rfl

theorem d_basis_eps1eps2_proved : d (basis .eps1eps2) = zero := by
  ext c_val
  unfold d zero
  rfl

theorem d_basis_eps1theta_proved : d (basis .eps1theta) = zero := by
  ext c_val
  unfold d zero
  rfl

theorem d_basis_eps2theta_proved : d (basis .eps2theta) = zero := by
  ext c_val
  unfold d zero
  rfl

theorem d_zero_is_zero : d zero = zero := by
  ext c_val
  unfold d zero
  rfl

theorem zero_mul_BasisAlgebra (a : BasisAlgebra) : mul zero a = zero := by
  ext x
  cases x <;> simp [mul, zero, add_zero, zero_add, one_mul, zero_mul, mul_zero]

theorem mul_zero_BasisAlgebra (a : BasisAlgebra) : mul a zero = zero := by
  ext x
  cases x <;> simp [mul, zero, add_zero, zero_add, one_mul, zero_mul, mul_zero]

theorem one_mul_any (b : NilpotentDGBasis) : mul (basis .one) (basis b) = basis b := by
  ext x
  simp only [mul, basis]
  cases b <;> cases x <;> simp

theorem mul_one_any (b : NilpotentDGBasis) : mul (basis b) (basis .one) = basis b := by
  ext x
  simp only [mul, basis]
  cases b <;> cases x <;> simp

theorem grade_basis (b : NilpotentDGBasis) : grade (basis b) = b.degree := by
  cases b with
  | one =>
    simp [grade, basis, NilpotentDGBasis.degree]
  | eps1 =>
    simp [grade, basis, NilpotentDGBasis.degree]
  | eps2 =>
    simp [grade, basis, NilpotentDGBasis.degree]
  | theta =>
    simp [grade, basis, NilpotentDGBasis.degree]
  | eps1eps2 =>
    simp [grade, basis, NilpotentDGBasis.degree]
  | eps1theta =>
    simp [grade, basis, NilpotentDGBasis.degree]
  | eps2theta =>
    simp [grade, basis, NilpotentDGBasis.degree]

theorem grade_mul_with_one (b : NilpotentDGBasis) :
  grade (mul (basis .one) (basis b)) = b.degree ∧
  grade (mul (basis b) (basis .one)) = b.degree := by
  constructor
  · rw [one_mul_any]; exact grade_basis b
  · rw [mul_one_any]; exact grade_basis b

theorem dot_mul_eq_mul_function (a b : BasisAlgebra) : a.mul b = mul a b := by
  rfl

theorem zero_eq_ring_zero : zero = (0 : BasisAlgebra) := rfl

theorem neg_zero_eq_zero : -(zero : BasisAlgebra) = zero := by
  ext b
  simp only [neg, zero]
  exact neg_zero

/-- Products giving zero due to nilpotency -/
theorem mul_eps1_eps1theta : mul (basis .eps1) (basis .eps1theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1theta_eps1 : mul (basis .eps1theta) (basis .eps1) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2_eps2theta : mul (basis .eps2) (basis .eps2theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2theta_eps2 : mul (basis .eps2theta) (basis .eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_theta_eps1theta : mul (basis .theta) (basis .eps1theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1theta_theta : mul (basis .eps1theta) (basis .theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_theta_eps2theta : mul (basis .theta) (basis .eps2theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2theta_theta : mul (basis .eps2theta) (basis .theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1eps2_eps1theta : mul (basis .eps1eps2) (basis .eps1theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1theta_eps1eps2 : mul (basis .eps1theta) (basis .eps1eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1eps2_eps2theta : mul (basis .eps1eps2) (basis .eps2theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2theta_eps1eps2 : mul (basis .eps2theta) (basis .eps1eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1theta_eps2theta : mul (basis .eps1theta) (basis .eps2theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2theta_eps1theta : mul (basis .eps2theta) (basis .eps1theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem eps1_mul_eps1eps2_is_zero : mul (basis .eps1) (basis .eps1eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem eps1eps2_mul_eps1_is_zero : mul (basis .eps1eps2) (basis .eps1) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2_eps1eps2_is_zero : mul (basis .eps2) (basis .eps1eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1eps2_eps2_is_zero : mul (basis .eps1eps2) (basis .eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1_eps2theta : mul (basis .eps1) (basis .eps2theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2_eps1theta : mul (basis .eps2) (basis .eps1theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2theta_eps1 : mul (basis .eps2theta) (basis .eps1) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1theta_eps2 : mul (basis .eps1theta) (basis .eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_theta_eps1eps2 : mul (basis .theta) (basis .eps1eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1theta_eps1theta_is_zero : mul (basis .eps1theta) (basis .eps1theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps2theta_eps2theta_is_zero : mul (basis .eps2theta) (basis .eps2theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem mul_eps1eps2_eps1eps2_is_zero : mul (basis .eps1eps2) (basis .eps1eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem pow_three : ((-1 : ℂ) ^ 3) = -1 := by norm_num

theorem neg_one_pow_two_eq_one : ((-1 : ℂ) ^ 2) = 1 := by norm_num

theorem one_smul (a : BasisAlgebra) : (1 : ℂ) • a = a := by
  ext x; exact one_mul (a x)

theorem neg_one_smul (a : BasisAlgebra) : (-1 : ℂ) • a = -a := by
  ext x; exact neg_one_mul (a x)

theorem smul_zero (c : ℂ) : c • (zero : BasisAlgebra) = zero := by
  ext x; exact mul_zero c

theorem neg_one_smul_zero : (-1 : ℂ) • (0 : BasisAlgebra) = 0 := by
  exact smul_zero (-1)

@[simp] theorem neg_one_smul_zero_simp : (-1 : ℂ) • (0 : BasisAlgebra) = 0 := neg_one_smul_zero

theorem h_eps1theta_eps1 : mul (basis .eps1theta) (basis .eps1) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem h_eps1theta_eps2 : mul (basis .eps1theta) (basis .eps2) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem h_eps2theta_eps1 : mul (basis .eps2theta) (basis .eps1) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem h_eps1eps2_eps1theta : mul (basis .eps1eps2) (basis .eps1theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

theorem h_eps1eps2_eps2theta : mul (basis .eps1eps2) (basis .eps2theta) = zero := by
  ext b; cases b <;> simp [mul, basis, zero]

instance instAddCommGroupBasisAlgebra : AddCommGroup BasisAlgebra where
  toAddGroup := inferInstance
  add_comm := fun a b => by ext x; exact add_comm (a x) (b x)

instance instRingBasisAlgebra : Ring BasisAlgebra where
  toMonoid := instMonoidBasisAlgebra
  toAddCommGroup := instAddCommGroupBasisAlgebra
  mul_zero := mul_zero_BasisAlgebra
  zero_mul := zero_mul_BasisAlgebra
  left_distrib := left_distrib_BasisAlgebra
  right_distrib := right_distrib_BasisAlgebra

instance instAlgebraBasisAlgebra : Algebra ℂ BasisAlgebra where
  algebraMap := {
    toFun := fun c_map => fun x => c_map * (if x = .one then 1 else 0),
    map_one' := by
      ext x
      show (fun x => (1 : ℂ) * (if x = .one then 1 else 0)) x = (one x)
      unfold one
      cases x <;> simp [one_mul]
    map_mul' := by
      intros c1 c2
      ext x
      show (fun x => (c1 * c2) * (if x = .one then 1 else 0)) x =
           (mul (fun x => c1 * (if x = .one then 1 else 0)) (fun x => c2 * (if x = .one then 1 else 0))) x
      unfold mul
      cases x <;> simp [mul_assoc]
    map_zero' := by
      ext x
      show (fun x => (0 : ℂ) * (if x = .one then 1 else 0)) x = (zero x)
      unfold zero
      cases x <;> simp [zero_mul]
    map_add' := by
      intros c1 c2
      ext x
      show (fun x => (c1 + c2) * (if x = .one then 1 else 0)) x =
           (add (fun x => c1 * (if x = .one then 1 else 0)) (fun x => c2 * (if x = .one then 1 else 0))) x
      unfold add
      cases x <;> simp [add_mul]
  }
  commutes' := by
    intro c a
    ext x
    show (mul (fun x => c * (if x = .one then 1 else 0)) a) x = (mul a (fun x => c * (if x = .one then 1 else 0))) x
    unfold mul
    cases x <;> simp [mul_comm]
  smul_def' := by
    intro c a
    ext x
    show (smul c a) x = (mul (fun x => c * (if x = .one then 1 else 0)) a) x
    unfold smul mul
    cases x <;> simp [mul_comm]

theorem smul_add (c : ℂ) (a b : BasisAlgebra) : c • (a + b) = c • a + c • b := by
  ext x; simp [smul, add, mul_add]

theorem add_smul (c d : ℂ) (a : BasisAlgebra) : (c + d) • a = c • a + d • a := by
  ext x
  show (c + d) * a x = c * a x + d * a x
  exact add_mul c d (a x)

theorem smul_smul (c d : ℂ) (a : BasisAlgebra) : c • (d • a) = (c * d) • a := by
  ext x
  show c * (d * a x) = (c * d) * a x
  exact (mul_assoc c d (a x)).symm

end BasisAlgebra

end RNT.Algebra
