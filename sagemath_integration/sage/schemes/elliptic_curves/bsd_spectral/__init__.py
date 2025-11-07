r"""
BSD Spectral Framework
=======================

This module provides tools for proving finiteness of Tate-Shafarevich groups
using spectral methods.

EXAMPLES::

    sage: from sage.schemes.elliptic_curves.bsd_spectral import SpectralFinitenessProver
    sage: E = EllipticCurve('11a1')
    sage: prover = SpectralFinitenessProver(E)
    sage: result = prover.prove_finiteness()
    sage: result['finiteness_proved']
    True
"""

from .spectral_finiteness import SpectralFinitenessProver, prove_sha_finiteness

__all__ = ['SpectralFinitenessProver', 'prove_sha_finiteness']
