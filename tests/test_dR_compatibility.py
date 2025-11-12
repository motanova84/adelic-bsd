# tests/test_dR_compatibility.py - SIMPLIFIED VERSION

r"""
(dR) Compatibility Tests (Simplified)
======================================

Basic tests for (dR) compatibility verification.

AUTHORS:

- Jose Manuel Mota Burruezo (2025-01)
"""

import pytest


def test_basic_dR_verification():
    """Test basic (dR) compatibility verification."""
    pytest.importorskip("sage")
    
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    
    try:
        from src.dR_compatibility import verify_dR_compatibility
        
        E = EllipticCurve('11a1')
        result = verify_dR_compatibility(E, 2)
        
        assert 'dR_compatible' in result
        assert isinstance(result['dR_compatible'], bool)
    
    except ImportError:
        pytest.skip("dR_compatibility module not available")


def test_dimension_computation():
    """Test dimension computation for (dR)."""
    pytest.importorskip("sage")
    
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    
    try:
        from src.dR_compatibility import compute_h1f_dimension
        
        E = EllipticCurve('11a1')
        dim = compute_h1f_dimension(E, 2)
        
        assert dim >= 0
        assert dim <= 2  # Typical range for elliptic curves
    
    except ImportError:
        pytest.skip("dR_compatibility module not available")


def test_good_reduction_case():
    """Test (dR) for good reduction."""
    pytest.importorskip("sage")
    
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    
    try:
        from src.dR_compatibility import verify_dR_compatibility
        
        E = EllipticCurve('11a1')
        result = verify_dR_compatibility(E, 2)
        
        assert result['dR_compatible']
        assert 'reduction_type' in result
    
    except ImportError:
        pytest.skip("dR_compatibility module not available")


def test_multiple_primes():
    """Test (dR) at multiple primes."""
    pytest.importorskip("sage")
    
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    
    try:
        from src.dR_compatibility import verify_dR_compatibility
        
        E = EllipticCurve('11a1')
        
        # Test at different primes
        primes = [2, 3, 5]
        N = E.conductor()
        
        for p in primes:
            if N % p != 0:  # Good reduction
                result = verify_dR_compatibility(E, p)
                assert 'dR_compatible' in result
    
    except ImportError:
        pytest.skip("dR_compatibility module not available")


def test_dR_dimensions_match():
    """Test that (dR) dimensions match."""
    pytest.importorskip("sage")
    
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    
    try:
        from src.dR_compatibility import (
            compute_h1f_dimension,
            compute_dR_dimension
        )
        
        E = EllipticCurve('11a1')
        p = 2
        
        dim_h1f = compute_h1f_dimension(E, p)
        dim_dR = compute_dR_dimension(E, p)
        
        # Compatibility means dimensions should match
        assert dim_h1f == dim_dR
    
    except ImportError:
        pytest.skip("dR_compatibility module not available")


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
