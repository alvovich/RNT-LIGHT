-- RNT/Algebra/Defs.lean
-- Aggregation file for Algebra module

import RNT.Algebra.Generators
import RNT.Algebra.Structure
import RNT.Algebra.BasisAlgebra
import RNT.Algebra.Operations
import RNT.Algebra.Instances
import RNT.Algebra.Homology

/-!
# Algebra Module

This module provides the nilpotent differential graded algebra A_ε for RNT-LIGHT.

## Main components

- `Generators`: Generators ε₁, ε₂, θ with nilpotency relations (RNT-LIGHT Section 1.1)
- `Structure`: Abstract structure of nilpotent DG-algebra (RNT-LIGHT Theorems T2-T3)
- `BasisAlgebra`: Concrete realization of A_ε with 7 basis elements (RNT-LIGHT Definition 1.2.1)
- `Operations`: Multiplication, grading, differential operations (RNT-LIGHT Theorem T2)
- `Instances`: Ring, Algebra, Module instances and dimension theorem (RNT-LIGHT Theorem T1)
- `Homology`: Homology computation H⁰≅ℂ, H¹≅ℂ², H²≅ℂ², H³≅ℂ (RNT-LIGHT Theorems 1.6-1.7)

## Structure

The Algebra module implements the nilpotent DG-algebra A_ε with:
- 7-dimensional basis: {1, ε₁, ε₂, θ, ε₁ε₂, ε₁θ, ε₂θ}
- Nilpotency relations: ε₁² = ε₂² = θ² = 0
- Critical relation: ε₁ε₂θ = 0
- Trivial differential: d ≡ 0
- Socle dimension: dim Soc(A_ε) = 3

## References

See RNT-LIGHT documentation (Section 1) for complete theoretical background.

## Tags

differential graded algebra, nilpotent algebra, homology, RNT-LIGHT
-/
