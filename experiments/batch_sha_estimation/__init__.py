"""
Batch Sha Estimation Module

Implements BSD-based estimation of |Ш(E)| (Tate-Shafarevich group cardinality)
for elliptic curves with rank ≥ 2.

Based on the BSD formula:
|Ш(E)| = L^{(r)}(E,1) / (r! * Ω_E * R_E * |Tors(E)|² * ∏c_p)

Where:
- L^{(r)}(E,1) = r-th derivative of L(E,s) at s=1 (r = rank of E)
- Ω_E = real period
- R_E = regulator (determinant of height pairing)
- Tors(E) = torsion subgroup
- ∏c_p = product of Tamagawa numbers
"""

from .estimate_sha import (
    estimate_sha,
    estimate_sha_from_curve,
    batch_estimate_sha,
    export_results_to_csv,
    ShaEstimationResult,
)

__all__ = [
    'estimate_sha',
    'estimate_sha_from_curve',
    'batch_estimate_sha',
    'export_results_to_csv',
    'ShaEstimationResult',
]
