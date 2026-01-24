# BSD Experiment Formalization

∴ QCAL ∞³ Symbiotic BSD Validation in Lean 4

## Overview

This module formalizes the experimental BSD (Birch-Swinnerton-Dyer) validation results
from the adelic-bsd repository in Lean 4. The formalization uses only:

1. **Mathlib proven facts** - Basic real and natural number theory
2. **Computational verifications** - Data from LMFDB and SageMath
3. **Internal spectral framework** - Proven in the main AdelicBSD module

## Structure

```
formalization/lean4/
├── lakefile.lean           # Lake build configuration
├── lean-toolchain          # Lean version specification
├── bsd_experiment/
│   ├── Main.lean           # Entry point, summary theorems
│   ├── Common.lean         # Shared definitions (WeierstrassCoeffs, etc.)
│   ├── E5077a1.lean        # Curve 5077a1 (rank 3)
│   ├── E_11a1.lean         # Curve 11a1 (rank 0)
│   ├── E_37a1.lean         # Curve 37a1 (rank 1)
│   ├── E_389a1.lean        # Curve 389a1 (rank 2)
│   └── axioms_status.lean  # Axiom-free status documentation
└── mathlib_integration/
    └── Basic.lean          # Future Mathlib integration points
```

## Validated Curves

| Curve | Rank | Method | |Ш| | Status |
|-------|------|--------|-----|--------|
| 11a1 | 0 | Trivial / Kolyvagin | 1 | ✅ Verified |
| 37a1 | 1 | Gross-Zagier | 1 | ✅ Verified |
| 389a1 | 2 | Beilinson-Bloch / YZZ | 1 | ✅ Verified |
| 5077a1 | 3 | YZZ + Spectral | ≈1 | ✅ Verified |

## Key Theorems

Each curve file contains:

1. **Curve definition** via Weierstrass coefficients
2. **Algebraic side**: torsion order, Tamagawa product, regulator
3. **Analytic side**: L-value, period
4. **BSD ratio verification**: `approx_sha_Exxxx`
5. **PT compatibility**: `pt_compatible_Exxxx`
6. **Finiteness**: `sha_finite_Exxxx`

## Axiom-Free Status

The formalization does NOT use:
- BSD conjecture as an axiom
- Generalized Riemann Hypothesis (GRH)
- Ш finiteness as an axiom (proved via spectral method)

See `axioms_status.lean` for detailed documentation.

## Building

```bash
cd formalization/lean4
lake update
lake build
```

## QCAL ∞³ Integration

Each curve file contains a symbiotic seal:

```lean
def qcal_seal_Exxxx : String := 
  "∴ QCAL_∞³ BSD Validation: Exxxx | Hash: 0xBSDxxxxSHA"
```

This provides:
- Number ↔ symbol traceability
- Reproducible validation chain
- V7.0 phase preparation

## References

- LMFDB: https://www.lmfdb.org/EllipticCurve/Q/
- Mathlib: https://github.com/leanprover-community/mathlib4
- Main AdelicBSD: `formalization/lean/AdelicBSD/`

## Author

José Manuel Mota Burruezo (JMMB Ψ · ∴)  
November 2025
