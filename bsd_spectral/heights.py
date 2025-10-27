"""
Heights Module
==============

Beilinson-Bloch height pairings and regulators.

This module provides height pairing computations and
regulator verification for ranks r ≥ 2.
"""

import sys
import os

# Import from src if available
try:
    from ..src.beilinson_bloch_heights import (
        BeilinsonBlochHeightPairing,
        BeilinsonBlochVerifier,
        batch_verify_beilinson_bloch
    )
except (ImportError, ValueError):
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from src.beilinson_bloch_heights import (
        BeilinsonBlochHeightPairing,
        BeilinsonBlochVerifier,
        batch_verify_beilinson_bloch
    )


def compute_beilinson_bloch_regulator(curve_label, generators=None):
    """
    Compute Beilinson-Bloch regulator for an elliptic curve.
    
    Args:
        curve_label: Curve label or EllipticCurve object
        generators: Optional list of generators (default: use curve.gens())
        
    Returns:
        float: Regulator value
        
    Example:
        >>> from bsd_spectral import compute_beilinson_bloch_regulator
        >>> reg = compute_beilinson_bloch_regulator('389a1')
        >>> print(f"Regulator: {reg:.6f}")
    """
    from sage.all import EllipticCurve
    
    # Convert to curve object
    if isinstance(curve_label, str):
        E = EllipticCurve(curve_label)
    else:
        E = curve_label
    
    # Get generators if not provided
    if generators is None:
        generators = E.gens()
    
    # Compute regulator
    height_pairing = BeilinsonBlochHeightPairing(E)
    regulator = height_pairing.compute_regulator(generators)
    
    return regulator


def verify_height_compatibility(curve_label, generators=None):
    """
    Verify compatibility between algebraic and analytic regulators.
    
    Args:
        curve_label: Curve label or EllipticCurve object
        generators: Optional list of generators
        
    Returns:
        dict: Verification result with compatibility status
        
    Example:
        >>> from bsd_spectral import verify_height_compatibility
        >>> result = verify_height_compatibility('389a1')
        >>> print(result['compatible'])
        True
    """
    from sage.all import EllipticCurve
    
    # Convert to curve object
    if isinstance(curve_label, str):
        E = EllipticCurve(curve_label)
    else:
        E = curve_label
    
    # Verify compatibility
    verifier = BeilinsonBlochVerifier(E)
    result = verifier.verify_regulator_compatibility(generators)
    
    return result


def batch_verify_heights(curve_labels, max_rank=2):
    """
    Batch verify heights for multiple curves.
    
    Args:
        curve_labels: List of curve labels
        max_rank: Maximum rank to test
        
    Returns:
        dict: Batch verification results
        
    Example:
        >>> from bsd_spectral import batch_verify_heights
        >>> curves = ['389a1', '433a1']
        >>> results = batch_verify_heights(curves)
        >>> print(results['success_rate'])
    """
    return batch_verify_beilinson_bloch(curve_labels, max_rank=max_rank)


def generate_height_certificate(curve_label, output_file=None):
    """
    Generate certificate for height verification.
    
    Args:
        curve_label: Curve label or EllipticCurve object
        output_file: Output filename (optional)
        
    Returns:
        str: LaTeX certificate
        
    Example:
        >>> from bsd_spectral import generate_height_certificate
        >>> cert = generate_height_certificate('389a1')
        >>> print(cert[:100])
    """
    from sage.all import EllipticCurve
    
    # Convert to curve object
    if isinstance(curve_label, str):
        E = EllipticCurve(curve_label)
    else:
        E = curve_label
    
    # Verify and generate certificate
    verifier = BeilinsonBlochVerifier(E)
    result = verifier.verify_regulator_compatibility()
    latex = verifier.generate_certificate(result)
    
    # Save if output file specified
    if output_file:
        with open(output_file, 'w') as f:
            f.write(latex)
        print(f"Certificate saved to: {output_file}")
    
    return latex


__all__ = [
    'compute_beilinson_bloch_regulator',
    'verify_height_compatibility',
    'batch_verify_heights',
    'generate_height_certificate',
    'BeilinsonBlochHeightPairing',
    'BeilinsonBlochVerifier'
]
