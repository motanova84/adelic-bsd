# SHA (Tate-Shafarevich) Group Estimation Validation

## Overview

This directory contains tools and results for analyzing the global coherence of |Ш(E)| estimates for elliptic curves with rank ≥ 2. The analysis detects potential numerical anomalies and generates meaningful visualizations.

## Scientific Objectives

### 1. Distribution Analysis
- Group curves by rank (r = 2, r = 3, ...)
- Generate histograms of:
  - Estimated values of |Ш(E)|
  - Natural logarithm: log|Ш(E)|
  - Comparison with L^(r)(1) and regulator R_E

### 2. Key Correlations
- log|Ш(E)| vs log(R_E) — Relationship between Sha and regulator
- log|Ш(E)| vs log(L^(r)(1)) — Connection to L-function derivatives
- log|Ш(E)| vs log(N_E) — Conductor dependence

### 3. Outlier Detection
- Curves with |Ш| very large or very small
- Cases where regulator or L-derivative are near zero (stability issues)

## Deep Mathematical Meaning

These correlations evaluate:
1. **BSD Formula Stability**: How stable is the BSD formula in derivatives of order r?
2. **Integrality of Ш**: Are |Ш| values integers or near-integers, as expected if BSD is true?
3. **Numerical Error Detection**: Can we identify curves where numerical errors have artificially inflated |Ш|?

If the regulator R_E is nearly zero, this can artificially inflate |Ш| estimates, leading to false positives. The analysis flags such cases for manual review.

## Files

| File | Description |
|------|-------------|
| `sha_analysis.py` | Main analysis script |
| `sha_estimates.csv` | Input data: curve labels, ranks, |Ш| estimates, regulators, L-derivatives |
| `log_sha_histogram.png` | Global histogram of log|Ш| distribution |
| `log_sha_histogram_rank{r}.png` | Per-rank histograms |
| `log_sha_vs_logR.png` | Correlation plot: log|Ш| vs log(R) |
| `log_sha_vs_logLr.png` | Correlation plot: log|Ш| vs log(L^(r)(1)) |
| `log_sha_vs_logN.png` | Correlation plot: log|Ш| vs log(N_E) |
| `outlier_report.txt` | Detailed report of detected anomalies |

## Usage

```bash
# Navigate to the validation directory
cd experiments/batch_sha_estimation/validation

# Run the analysis
python sha_analysis.py
```

## CSV Format

The input CSV file (`sha_estimates.csv`) must have the following columns:

| Column | Required | Description |
|--------|----------|-------------|
| `curve_label` | No | LMFDB label for the curve |
| `rank` | No | Algebraic rank of the curve |
| `sha_estimate` | **Yes** | Estimated |Ш(E)| value |
| `R` | **Yes** | Regulator R_E |
| `l_derivative` | **Yes** | L^(r)(1) value |
| `conductor` | No | Conductor N_E |

## Preliminary Observations

### Expected Behavior
- For BSD-valid curves, |Ш| should be a perfect square
- log|Ш| should show a relatively normal distribution
- Strong correlation between log|Ш| and log(R) is expected from the BSD formula

### Warning Signs
- |Ш| values that are not near perfect squares
- Extreme outliers in the log|Ш| distribution
- Very small regulators leading to inflated |Ш| estimates
- Weak or negative correlation where positive is expected

## Theoretical Background

The Birch-Swinnerton-Dyer conjecture predicts:

```
L^(r)(E, 1) / r! = (Ω_E · R_E · |Ш(E)| · ∏c_p) / |E(Q)_tors|²
```

Rearranging for |Ш|:

```
|Ш(E)| = (L^(r)(1) · |E(Q)_tors|² · r!) / (Ω_E · R_E · ∏c_p)
```

This shows that:
- Small R_E → Large |Ш| estimate (potential instability)
- Small L^(r)(1) → Small |Ш| estimate
- The correlation between log|Ш| and log(R) should be approximately -1

## References

1. Birch, B. J., & Swinnerton-Dyer, H. P. F. (1965). Notes on elliptic curves. II. *J. reine angew. Math.*, 218, 79-108.
2. Cremona, J. E. (1997). *Algorithms for Modular Elliptic Curves*. Cambridge University Press.
3. Stein, W., & Watkins, M. (2002). A Database of Elliptic Curves—First Report. *Algorithmic Number Theory*, LNCS 2369, 267-275.

## Author

José Manuel Mota Burruezo (JMMB Ψ · ∴)

Date: November 2025
