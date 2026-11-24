import Lake
open Lake DSL

package MitakaFixedPoint where
  description := "Kernel-checked analysis of the fixed-point Mitaka sampler (ePrint 2026/2521)"
  license := "Apache-2.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩
  ]

require VCVio from git "https://github.com/Verified-zkEVM/VCVio" @
  "f1e63c780de398fb62206dd5890f27e1ad64e0e6"

/-- Modules vendored from FalconPrecision 0.4.0
(https://github.com/XC0R/falcon-fixed-point-security-lean, commit 1303738); see README.md. -/
lean_lib FalconPrecision where
  globs := #[.submodules `FalconPrecision]

@[default_target]
lean_lib Mitaka where
  globs := #[.andSubmodules `Mitaka]
