import Lake
open Lake DSL

package RNT where
  -- Removed problematic link flags that may mask errors
  -- moreLinkArgs := #["-L./.lake/packages/LeanInfer/build/lib", "-lonnxruntime", "-lctranslate2"]

-- Main library as default target
@[default_target]
lean_lib RNT where
  -- Add strict compiler settings
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`diagnostics, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`warningAsError, true⟩,
    -- Disable linters unnecessary for theoretical work
    ⟨`linter.style.longLine, false⟩,
    ⟨`linter.upstreamableDecl, false⟩,
    ⟨`linter.minImports, false⟩,
    ⟨`linter.ppRoundtrip, false⟩,
    ⟨`linter.style.refine, false⟩,
    ⟨`linter.missingDocs, false⟩,
    -- Disable heartbeat information (linters, not trace!)
    ⟨`linter.countHeartbeats, false⟩,
    ⟨`linter.countHeartbeatsApprox, false⟩,
    ⟨`linter.flexible, false⟩
  ]

-- Add Mathlib
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Add Batteries according to official documentation
require "leanprover-community" / "batteries" @ git "main"

-- Executable for checking dependencies
lean_exe check_all where
  root := `Main
