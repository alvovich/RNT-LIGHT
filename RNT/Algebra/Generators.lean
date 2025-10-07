-- RNT/Algebra/Generators.lean
-- Generators and basis elements of the nilpotent differential graded algebra A_ε

import RNT.Basic

namespace RNT.Algebra

/-- Generators of the nilpotent DG-algebra A_ε.
Three generators: ε₁, ε₂ (degree 1) and θ (degree 2) as in RNT-LIGHT Section 1.1. -/
inductive NilpotentDGGenerator
  | ε₁ | ε₂ | θ
  deriving DecidableEq

instance : Fintype NilpotentDGGenerator where
  elems := {NilpotentDGGenerator.ε₁, NilpotentDGGenerator.ε₂, NilpotentDGGenerator.θ}
  complete := fun x => by cases x <;> simp [Finset.mem_insert, Finset.mem_singleton]

/-- Degrees of generators: deg(ε₁) = deg(ε₂) = 1, deg(θ) = 2. -/
def NilpotentDGGenerator.degree : NilpotentDGGenerator → ℕ
  | .ε₁ => 1 | .ε₂ => 1 | .θ => 2

/-- Basis of the nilpotent DG-algebra A_ε.
Seven basis elements {1, ε₁, ε₂, θ, ε₁ε₂, ε₁θ, ε₂θ} with degrees 0,1,1,2,2,3,3
as specified in RNT-LIGHT Section 1.2. This gives dim_ℂ(A_ε) = 7. -/
inductive NilpotentDGBasis
  | one | eps1 | eps2 | theta | eps1eps2 | eps1theta | eps2theta
  deriving DecidableEq

instance : Fintype NilpotentDGBasis where
  elems := {NilpotentDGBasis.one, NilpotentDGBasis.eps1, NilpotentDGBasis.eps2, NilpotentDGBasis.theta, NilpotentDGBasis.eps1eps2, NilpotentDGBasis.eps1theta, NilpotentDGBasis.eps2theta}
  complete := fun x => by cases x <;> simp [Finset.mem_insert, Finset.mem_singleton]

/-- Degrees of basis elements. -/
def NilpotentDGBasis.degree : NilpotentDGBasis → ℕ
  | .one => 0 | .eps1 => 1 | .eps2 => 1 | .theta => 2
  | .eps1eps2 => 2 | .eps1theta => 3 | .eps2theta => 3

end RNT.Algebra
