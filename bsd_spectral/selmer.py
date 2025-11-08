"""
Selmer Module
=============

Advanced Selmer map verification with p-adic cohomology.

This module provides tools for verifying the Selmer map
and its compatibility with Galois cohomology structures.
"""

import sys
import os

# Import from src if available
try:
    from ..src.verification.selmer_verification import (
        verify_selmer_maps as _verify_selmer_maps,
        batch_verify_selmer_maps as _batch_verify_selmer_maps
    )
    from ..src.padic_comparison import FontainePerrinRiouCompatibility
except (ImportError, ValueError):
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from src.verification.selmer_verification import (
        verify_selmer_maps as _verify_selmer_maps,
        batch_verify_selmer_maps as _batch_verify_selmer_maps
    )
    from src.padic_comparison import FontainePerrinRiouCompatibility


def verify_selmer_maps(curve_label, primes=None, precision=20):
    """
    Verify Selmer map for an elliptic curve.
    
    Args:
        curve_label: Curve label (e.g., '11a1') or EllipticCurve object
        primes: List of primes to check (default: [2, 3, 5])
        precision: p-adic precision
        
    Returns:
        dict: Verification certificate
        
    Example:
        >>> from bsd_spectral import verify_selmer_maps
        >>> cert = verify_selmer_maps('11a1', primes=[2, 3])
        >>> print(cert['verification_passed'])
        True
    """
    if primes is None:
        primes = [2, 3, 5]
    
    return _verify_selmer_maps(curve_label, primes=primes, precision=precision)


def batch_verify_selmer_maps(curve_labels, primes=None):
    """
    Batch verify Selmer maps for multiple curves.
    
    Args:
        curve_labels: List of curve labels
        primes: List of primes to check
        
    Returns:
        dict: Batch verification results
        
    Example:
        >>> from bsd_spectral import batch_verify_selmer_maps
        >>> curves = ['11a1', '37a1']
        >>> results = batch_verify_selmer_maps(curves, primes=[2])
        >>> print(results['success_rate'])
    """
    if primes is None:
        primes = [2, 3]
    
    return _batch_verify_selmer_maps(curve_labels, primes=primes)


def generate_selmer_certificate(curve_label, primes=None, output_file=None):
    """
    Generate certificate for Selmer map verification.
    
    Args:
        curve_label: Curve label or EllipticCurve object
        primes: List of primes
        output_file: Output filename (optional)
        
    Returns:
        str: LaTeX certificate
        
    Example:
        >>> from bsd_spectral import generate_selmer_certificate
        >>> cert = generate_selmer_certificate('11a1')
        >>> print(cert[:100])
    """
    from sage.all import EllipticCurve
    
    if primes is None:
        primes = [2, 3, 5]
    
    # Convert to curve object
    if isinstance(curve_label, str):
        E = EllipticCurve(curve_label)
    else:
        E = curve_label
    
    # Verify and generate certificate
    result = verify_selmer_maps(E, primes=primes)
    
    # Generate LaTeX using FontainePerrinRiouCompatibility
    checker = FontainePerrinRiouCompatibility(E, primes)
    compat_result = checker.verify_compatibility()
    latex = checker.generate_certificate(compat_result)
    
    # Save if output file specified
    if output_file:
        with open(output_file, 'w') as f:
            f.write(latex)
        print(f"Certificate saved to: {output_file}")
    
    return latex


__all__ = [
    'verify_selmer_maps',
    'batch_verify_selmer_maps',
    'generate_selmer_certificate'
]
