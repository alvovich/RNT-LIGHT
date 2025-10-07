-- RNT/Core/Defs.lean
-- Aggregation file for Core module

import RNT.Core.DirectedSystem
import RNT.Core.BraidedCategory
import RNT.Core.UniversalSystem
import RNT.Core.Integration

/-!
# Core Module

This module provides the core mathematical foundations for RNT-LIGHT.

## Main components

- `DirectedSystem`: Implementation of directed systems and colimits (RNT-LIGHT Section 3.1)
- `BraidedCategory`: Braided ∞-categories with tensor products and braiding (RNT-LIGHT Definition 1.3.1)
- `UniversalSystem`: Universal systems ℌ = (X, P, Φ, I, 𝒜) (RNT-LIGHT Section 3.2)
- `Integration`: Integration of all RNT-LIGHT components

## Structure

The Core module establishes the foundational categorical and topological structures
required for RNT-LIGHT, providing the mathematical machinery for invariants,
morphisms, and their compositions.

## References

See RNT-LIGHT documentation (Sections 1-3) for complete theoretical background.

## Tags

category theory, braided categories, directed systems, universal systems, RNT-LIGHT
-/
