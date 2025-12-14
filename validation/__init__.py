"""
Validation Module for Adelic BSD Framework

This module provides validation scripts for verifying properties
of elliptic curves and the Birch-Swinnerton-Dyer conjecture.

Modules:
--------
- l_function_bsd_check: L-function computation and BSD partial validation
"""

__version__ = '0.1.0'
__author__ = 'Mota Burruezo'
BSD Validation Module

This module provides validation scripts for the Birch and Swinnerton-Dyer
conjecture computations.
"""
Validation Module

Scripts for validating BSD formula components and estimating Sha values.
"""

from .birch_swinnerton_sha import (
    estimate_sha,
    ShaEstimator,
    compute_bsd_lhs,
    compute_bsd_rhs,
    validate_sha_estimation
)

__all__ = [
    'estimate_sha',
    'ShaEstimator',
    'compute_bsd_lhs',
    'compute_bsd_rhs',
    'validate_sha_estimation'
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
