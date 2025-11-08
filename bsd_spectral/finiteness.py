"""
Finiteness Module
=================

Spectral finiteness proofs for Tate-Shafarevich groups.

This module wraps the core spectral finiteness functionality
from the main framework into a clean, installable package.
"""

import sys
import os

# Import from src if available
try:
    # Try relative import first (when installed as package)
    from ..src.spectral_finiteness import (
        SpectralFinitenessProver,
        prove_finiteness_for_curve as _prove_finiteness_for_curve,
        batch_prove_finiteness as _batch_prove_finiteness
    )
except (ImportError, ValueError):
    # Fallback to absolute import (development mode)
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from src.spectral_finiteness import (
        SpectralFinitenessProver,
        prove_finiteness_for_curve as _prove_finiteness_for_curve,
        batch_prove_finiteness as _batch_prove_finiteness
    )


def prove_finiteness(curve_label, primes=None, precision=20):
    """
    Prove finiteness of Sha(E/Q) for an elliptic curve.
    
    Args:
        curve_label: Curve label (e.g., '11a1') or EllipticCurve object
        primes: List of primes to check (default: conductor-based selection)
        precision: Numerical precision
        
    Returns:
        dict: Proof result with finiteness status and global bound
        
    Example:
        >>> from bsd_spectral import prove_finiteness
        >>> result = prove_finiteness('11a1')
        >>> print(result['finiteness_proved'])
        True
    """
    from sage.all import EllipticCurve
    
    # Convert to curve object if needed
    if isinstance(curve_label, str):
        E = EllipticCurve(curve_label)
    else:
        E = curve_label
    
    # Create prover
    prover = SpectralFinitenessProver(E)
    
    # Run proof
    result = prover.prove_finiteness()
    
    return result


def batch_prove_finiteness(curve_labels, output_dir=None):
    """
    Prove finiteness for multiple curves.
    
    Args:
        curve_labels: List of curve labels
        output_dir: Directory for certificates (optional)
        
    Returns:
        dict: Batch results with success rate
        
    Example:
        >>> from bsd_spectral import batch_prove_finiteness
        >>> curves = ['11a1', '37a1', '389a1']
        >>> results = batch_prove_finiteness(curves)
        >>> print(f"Success rate: {results['success_rate']}")
    """
    return _batch_prove_finiteness(curve_labels, output_dir=output_dir)


def generate_finiteness_certificate(curve_label, output_file=None):
    """
    Generate LaTeX certificate for finiteness proof.
    
    Args:
        curve_label: Curve label or EllipticCurve object
        output_file: Output filename (default: auto-generated)
        
    Returns:
        str: LaTeX certificate content
        
    Example:
        >>> from bsd_spectral import generate_finiteness_certificate
        >>> cert = generate_finiteness_certificate('11a1')
        >>> print(cert[:100])
    """
    from sage.all import EllipticCurve
    
    # Convert to curve object if needed
    if isinstance(curve_label, str):
        E = EllipticCurve(curve_label)
        label = curve_label
    else:
        E = curve_label
        label = str(E)
    
    # Create prover and generate certificate
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()
    
    # Generate LaTeX
    latex = prover.generate_certificate()
    
    # Save if output file specified
    if output_file:
        with open(output_file, 'w') as f:
            f.write(latex)
        print(f"Certificate saved to: {output_file}")
    
    return latex


__all__ = [
    'prove_finiteness',
    'batch_prove_finiteness',
    'generate_finiteness_certificate',
    'SpectralFinitenessProver'
]
