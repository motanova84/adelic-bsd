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
    SpectralFinitenessProver
)

from sage.schemes.elliptic_curves.bsd_spectral.dR_compatibility import (
    verify_dR_compatibility,
    prove_dR_all_cases
)

from sage.schemes.elliptic_curves.bsd_spectral.PT_compatibility import (
    verify_PT_compatibility,
    prove_PT_all_ranks
)

from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import (
    CompleteDRCompatibility,
    CompletePTCompatibility,
    verify_dR_complete,
    verify_PT_complete
)

__all__ = [
    'SpectralFinitenessProver',
    'verify_dR_compatibility',
    'prove_dR_all_cases',
    'verify_PT_compatibility',
    'prove_PT_all_ranks',
    'CompleteDRCompatibility',
    'CompletePTCompatibility',
    'verify_dR_complete',
    'verify_PT_complete'
]
