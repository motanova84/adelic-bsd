r"""
BSD Spectral Framework

This module provides spectral-adelic framework functions for
verifying BSD compatibility statements.

EXAMPLES::

    sage: from sage.schemes.elliptic_curves.bsd_spectral import verify_PT_compatibility
    sage: E = EllipticCurve('37a1')
    sage: result = verify_PT_compatibility(E)
    sage: result['PT_compatible']
    True
"""

from .PT_compatibility import (
    compute_gross_zagier_height,
    compute_yzz_height,
    verify_PT_compatibility
)

__all__ = [
    'compute_gross_zagier_height',
    'compute_yzz_height',
    'verify_PT_compatibility'
]
