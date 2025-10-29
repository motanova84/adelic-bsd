# dR Uniformity Certificates

This directory contains verification certificates for the Fontaine–Perrin-Riou dR compatibility condition.

## Overview

Each certificate validates the correspondence:

$$\dim H^1_f(Q_p, V_p) = \dim D_{\mathrm{dR}}(V_p)/\mathrm{Fil}^0$$

for a specific elliptic curve at primes p = 2, 3, 5.

## Certificate Formats

Each curve has two certificate files:

- **`.json` format**: Machine-readable certificate with complete verification data
- **`.tex` format**: LaTeX certificate for human-readable documentation

## Certificate Contents

Each certificate includes:

1. **Curve metadata**: Label, conductor, rank
2. **Prime-by-prime verification**: 
   - Dimension of H¹f (Bloch-Kato Selmer condition)
   - Dimension of D_dR/Fil⁰ (filtered de Rham cohomology)
   - Reduction type at each prime
   - Compatibility status
3. **Overall status**: ✅ (fully compatible) or ⚠️ (deviations present)
4. **Notes**: Explanations of any deviations

## Sample Certificates

This directory contains sample certificates for:

- **11a1**: Good reduction, perfect correspondence
- **37a1**: Rank 1 reference curve
- **24a1**: Warning case (deviation at p=2)
- **389a1**: Rank 2 high-precision reference
- **990h1**: Warning case (deviation at p=5)

## Generating All Certificates

To generate certificates for all 20 test curves:

```bash
sage -python scripts/validate_dR_uniformity.py
```

This will create:
- Individual `.tex` and `.json` certificates for each curve
- Complete results in `validation_dR_uniformity_results.json`

## Validation

Certificate integrity can be verified by checking:
1. Dimensions are non-negative integers
2. Reduction types match expected values for the conductor
3. Compatibility flag matches dimensional equality
4. Deviation equals |h1f_dim - dR_dim|

## References

- J.-M. Fontaine, *Représentations p-adiques semi-stables*, 1994
- B. Perrin-Riou, *Fonctions L p-adiques des représentations p-adiques*, 1995
- S. Bloch – K. Kato, *L-functions and Tamagawa numbers*, 1990
