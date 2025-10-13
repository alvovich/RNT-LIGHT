-- RNT/Core/UniversalSystem.lean
-- Universal system structure (RNT-LIGHT Section 3.2)

import RNT.Basic
import RNT.Core.DirectedSystem
import RNT.Core.BraidedCategory

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

open CategoryTheory

namespace RNT.Core

/-- Universal system as formalized in RNT-LIGHT Section 3.2.
A universal system ℌ = (X, P, Φ, I, 𝒜) consists of:
- X: colimit of state spaces X_s
- P: colimit of parameter spaces P_s
- Φ: X × P → X joint continuous evolution map
- I: X → 𝒜 functor into symmetric monoidal category
- 𝒜: symmetric monoidal category of invariants -/
structure UniversalSystem (S_type : Type*) (dirS_inst : DirectedSystem S_type) where
  X_family : StateSpaceFamily S_type dirS_inst
  P_family : ParameterFamily S_type dirS_inst
  X : Type*
  X_topology : TopologicalSpace X
  X_metric : PseudoMetricSpace X
  X_family_metrics : ∀ (s : S_type), PseudoMetricSpace (X_family.space s)
  X_metric_compatible : ∀ (s : S_type), ∃ (embed : X_family.space s → X),
    (∀ x y, @dist (X_family.space s) (X_family_metrics s).toDist x y = dist (embed x) (embed y)) ∧
    (@Continuous (X_family.space s) X (X_family.topology s) X_topology embed)
  X_inclusion : ∀ (s : S_type), (X_family.space s) → X
  X_inclusion_continuous : ∀ (s : S_type),
    @Continuous (X_family.space s) X (X_family.topology s) X_topology (X_inclusion s)
  X_inclusion_compat : ∀ {s₁ s₂ : S_type} (h : dirS_inst.order.le s₁ s₂) (x : X_family.space s₁),
    X_inclusion s₂ (X_family.map h x) = X_inclusion s₁ x
  P : Type*
  P_order_univ : PartialOrder P
  P_topology : TopologicalSpace P
  /-- P has colimit topology: V open in P iff each inclusion⁻¹(V) open in P_s -/
  P_colimit_topology : ∃ (inclusion_maps : ∀ s, P_family.param s → P),
    ∀ (V : Set P), @IsOpen P P_topology V ↔ ∀ s, @IsOpen (P_family.param s) (P_family.topology s) ((inclusion_maps s) ⁻¹' V)
  P_inclusion : ∀ (s : S_type), (P_family.param s) → P
  P_inclusion_monotone : ∀ (s : S_type),
    @Monotone (P_family.param s) P (P_family.order_param s).toPreorder P_order_univ.toPreorder (P_inclusion s)
  P_inclusion_compat : ∀ {s₁ s₂ : S_type} (h : dirS_inst.order.le s₁ s₂) (p : P_family.param s₁),
    P_inclusion s₂ (P_family.map h p) = P_inclusion s₁ p
  /-- Universal property of colimit X: continuous maps out of X are uniquely determined
  by compatible continuous maps out of each X_s -/
  X_universal : ∀ {Z : Type*} (_Z_topology : TopologicalSpace Z)
    (f_map : ∀ (s : S_type), (X_family.space s) → Z)
    (_f_continuous_map : ∀ (s : S_type), @Continuous (X_family.space s) Z (X_family.topology s) _Z_topology (f_map s))
    (_f_compat : ∀ {s₁ s₂ : S_type} (h : dirS_inst.order.le s₁ s₂) (x : X_family.space s₁),
      f_map s₂ (X_family.map h x) = f_map s₁ x),
    ∃! (g : X → Z), (∀ (s : S_type) (x : X_family.space s), g (X_inclusion s x) = f_map s x) ∧
    @Continuous X Z X_topology _Z_topology g
  /-- Universal property of colimit P: monotone maps out of P are uniquely determined
  by compatible monotone maps out of each P_s -/
  P_universal : ∀ {Q : Type*} (Q_order : PartialOrder Q)
    (f_map : ∀ (s : S_type), (P_family.param s) → Q)
    (_f_monotone_map : ∀ (s : S_type), @Monotone (P_family.param s) Q (P_family.order_param s).toPreorder Q_order.toPreorder (f_map s))
    (_f_compat : ∀ {s₁ s₂ : S_type} (h : dirS_inst.order.le s₁ s₂) (p : P_family.param s₁),
      f_map s₂ (P_family.map h p) = f_map s₁ p),
    ∃! (g : P → Q), (∀ (s : S_type) (p : P_family.param s), g (P_inclusion s p) = f_map s p) ∧
    @Monotone P Q P_order_univ.toPreorder Q_order.toPreorder g
  /-- Symmetric monoidal category of invariants (RNT-LIGHT Section 2) -/
  𝒜 : BraidedInfinityCategory
  /-- Invariant functor I: X → 𝒜 mapping each state to its algebra of invariants -/
  I : X → 𝒜.objects
  /-- Evolution map Φ: X × P → X (RNT-LIGHT Section 3) -/
  Phi : X → P → X
  /-- Joint continuity: Φ: X × P → X continuous with respect to product topology -/
  Phi_joint_continuous : @Continuous (X × P) X (instTopologicalSpaceProd) X_topology (fun (x_p : X × P) => Phi x_p.1 x_p.2)
  /-- For each p ∈ P, the map Φ(·, p): X → X is a homeomorphism -/
  Phi_homeomorph : P → X ≃ₜ X
  Phi_homeomorph_apply : ∀ (p : P) (x : X), (Phi_homeomorph p) x = Phi x p

end RNT.Core
