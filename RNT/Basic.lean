-- RNT/Basic.lean
-- Basic imports and auxiliary definitions for Resonant Nilpotence Theory - LIGHT version

-- Basic modules for complex numbers and topological spaces
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Basic

-- Modules for categories and monoidal structures
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Iso

-- Modules for algebraic structures
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Quotient
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.StdBasis

-- Modules for colimits and other categorical constructions
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types

-- Additional modules
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Data.Complex.Module

open CategoryTheory
open Complex
open Filter Topology

namespace RNT

-- Disable binder annotation checking for simplification
set_option checkBinderAnnotations false

-- Auxiliary lemmas for complex numbers
theorem neg_one_pow_four : ((-1 : ℂ) ^ 4) = 1 := by norm_num
theorem neg_one_pow_three : ((-1 : ℂ) ^ 3) = -1 := by norm_num
theorem neg_one_pow_two_eq_one : ((-1 : ℂ) ^ 2) = 1 := by norm_num

end RNT

def hello := "world"
