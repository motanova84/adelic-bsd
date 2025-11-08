r"""
Convenience imports for BSD Spectral Framework
===============================================

This module provides convenient access to all public functions in the
BSD spectral framework.

EXAMPLES::

    sage: from sage.schemes.elliptic_curves.bsd_spectral.all import *
    sage: E = EllipticCurve('11a1')
    sage: prover = SpectralFinitenessProver(E)
    sage: result = prover.prove_finiteness()
    sage: result['finiteness_proved']
    True
"""

from sage.schemes.elliptic_curves.bsd_spectral.spectral_finiteness import (
    SpectralFinitenessProver,
    prove_sha_finiteness
)

from sage.schemes.elliptic_curves.bsd_spectral.dR_compatibility import (
    verify_dR_compatibility,
    prove_dR_all_cases,
    compute_h1f_dimension,
    compute_dR_dimension
)

from sage.schemes.elliptic_curves.bsd_spectral.PT_compatibility import (
    verify_PT_compatibility,
    compute_gross_zagier_height,
    compute_yzz_height
)

__all__ = [
    'SpectralFinitenessProver',
    'prove_sha_finiteness',
    'verify_dR_compatibility',
    'prove_dR_all_cases',
    'compute_h1f_dimension',
    'compute_dR_dimension',
    'verify_PT_compatibility',
    'compute_gross_zagier_height',
    'compute_yzz_height'
]
