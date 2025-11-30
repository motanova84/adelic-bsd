"""
Batch SHA Estimation Module

Computes |Ш(E)| (Tate-Shafarevich group cardinality) for elliptic curves
with rank ≥ 2 using the BSD formula.

BSD Formula:
    |Ш(E)| = L^{(r)}(E,1) / (r! · Ω_E · R_E · |Tors(E)|² · ∏c_p)

Where:
    - L^{(r)}(E,1) = r-th derivative of L(E,s) at s=1
    - r = rank of E
    - Ω_E = real period
    - R_E = regulator (determinant of height pairing matrix)
    - Tors(E) = torsion subgroup
    - ∏c_p = product of Tamagawa numbers
"""

from .estimate_sha import estimate_sha, batch_sha_estimation, ShaEstimator

__all__ = ['estimate_sha', 'batch_sha_estimation', 'ShaEstimator']
