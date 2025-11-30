"""
BSD Experimental Validation Module
===================================

This module implements experimental validation of the Birch and Swinnerton-Dyer
conjecture on elliptic curves not contained in LMFDB or not covered by classical
proofs (rank ≥ 2, large conductor, non-trivially known coefficients).

Main features:
- Generation of non-standard elliptic curves with specified invariants
- Complete BSD formula computation (L(E,1), Ω, regulator, torsion, Tamagawa, Sha)
- Comparison of LHS vs RHS of BSD formula
- QCAL seal validation with cryptographic hashes

Author: BSD Spectral Framework
Date: November 2025
"""

from .bsd_experiment import (
    BSDExperiment,
    compute_bsd_comparison,
    generate_curve_json,
    run_bsd_experiment,
)
from .curve_generator import (
    generate_experimental_curves,
    get_experimental_curve_definitions,
)
from .qcal_seal import (
    generate_qcal_seal,
    verify_qcal_seal,
)
from .summary_generator import (
    generate_summary_csv,
    generate_readme_genesis,
)

__all__ = [
    'BSDExperiment',
    'compute_bsd_comparison',
    'generate_curve_json',
    'run_bsd_experiment',
    'generate_experimental_curves',
    'get_experimental_curve_definitions',
    'generate_qcal_seal',
    'verify_qcal_seal',
    'generate_summary_csv',
    'generate_readme_genesis',
]
