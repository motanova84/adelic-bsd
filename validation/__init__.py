"""
Validation module for BSD conjecture verification.

This module contains scripts for validating the Birch and Swinnerton-Dyer
conjecture computations.
"""

from .birch_swinnerton_lhs import (
    BirchSwinnertonLHS,
    compute_bsd_lhs_vs_rhs,
    validate_bsd_comparison
)

__all__ = [
    'BirchSwinnertonLHS',
    'compute_bsd_lhs_vs_rhs',
    'validate_bsd_comparison'
]
