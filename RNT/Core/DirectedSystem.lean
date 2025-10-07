-- RNT/Core/DirectedSystem.lean
-- Directed systems, state space families, and parameter families (RNT-LIGHT Section 3.1)

import RNT.Basic

namespace RNT.Core

/-- Directed system: a partially ordered set S where every pair has an upper bound.
Used to index families of spaces and parameters in RNT-LIGHT Section 3.1. -/
structure DirectedSystem (S : Type*) where
  order : PartialOrder S
  directed : ∀ (s₁ s₂ : S), ∃ (s₃ : S), order.le s₁ s₃ ∧ order.le s₂ s₃

/-- State space family: topological spaces X_s indexed by a directed system S,
with continuous structure maps compatible with the partial order. -/
structure StateSpaceFamily (S : Type*) (dirS : DirectedSystem S) where
  space : S → Type*
  topology : ∀ (s : S), TopologicalSpace (space s)
  map : ∀ {s₁ s₂ : S} (_h : dirS.order.le s₁ s₂), space s₁ → space s₂
  map_continuous : ∀ {s₁ s₂ : S} (_h : dirS.order.le s₁ s₂),
    haveI : TopologicalSpace (space s₁) := topology s₁
    haveI : TopologicalSpace (space s₂) := topology s₂
    Continuous (map _h)
  map_id : ∀ (s : S),
    letI := dirS.order.toPreorder
    map (le_refl s) = id
  map_comp : ∀ {s₁ s₂ s₃ : S} (_h₁₂ : dirS.order.le s₁ s₂) (_h₂₃ : dirS.order.le s₂ s₃),
    letI := dirS.order.toPreorder
    Function.comp (map _h₂₃) (map _h₁₂) = map (le_trans _h₁₂ _h₂₃)

/-- Parameter family: partially ordered sets P_s with order topology,
indexed by a directed system S, with monotone and continuous structure maps. -/
structure ParameterFamily (S : Type*) (dirS : DirectedSystem S) where
  param : S → Type*
  order_param : ∀ (s : S), PartialOrder (param s)
  topology : ∀ (s : S), TopologicalSpace (param s)
  map : ∀ {s₁ s₂ : S} (_h : dirS.order.le s₁ s₂), param s₁ → param s₂
  map_monotone : ∀ {s₁ s₂ : S} (_h : dirS.order.le s₁ s₂),
    haveI : Preorder (param s₁) := (order_param s₁).toPreorder
    haveI : Preorder (param s₂) := (order_param s₂).toPreorder
    Monotone (map _h)
  map_continuous : ∀ {s₁ s₂ : S} (_h : dirS.order.le s₁ s₂),
    haveI : TopologicalSpace (param s₁) := topology s₁
    haveI : TopologicalSpace (param s₂) := topology s₂
    Continuous (map _h)
  order_topology : ∀ (s : S), @OrderTopology (param s) (topology s) (order_param s).toPreorder
  map_id : ∀ (s : S),
    letI := dirS.order.toPreorder
    map (le_refl s) = id
  map_comp : ∀ {s₁ s₂ s₃ : S} (_h₁₂ : dirS.order.le s₁ s₂) (_h₂₃ : dirS.order.le s₂ s₃),
    letI := dirS.order.toPreorder
    Function.comp (map _h₂₃) (map _h₁₂) = map (le_trans _h₁₂ _h₂₃)

end RNT.Core
