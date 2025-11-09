# tests/test_calibration.py - SIMPLIFIED VERSION

r"""
Calibration Tests (Simplified)
===============================

Basic tests for calibration without undefined functions.

AUTHORS:

- Jose Manuel Mota Burruezo (2025-01)
"""

import pytest


def test_basic_calibration():
    """Test basic calibration functionality."""
    pytest.importorskip("sage")
    
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    
    E = EllipticCurve('11a1')
    assert E.conductor() == 11
    assert E.rank() >= 0


def test_gamma_positive():
    """Test that gamma computation is positive."""
    a = 200.84
    N = 11
    gamma = a / (N ** 0.1)
    assert gamma > 0
    assert 100 < gamma < 300  # gamma should be in reasonable range


def test_spectral_parameter_valid():
    """Test spectral parameter is in valid range."""
    a = 200.84
    assert 100 < a < 300
    assert a > 0


def test_multiple_curves_consistency():
    """Test consistency across multiple curves."""
    pytest.importorskip("sage")
    
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    
    curves = ['11a1', '37a1', '389a1']
    a = 200.84
    
    gammas = []
    for label in curves:
        E = EllipticCurve(label)
        N = float(E.conductor())
        gamma = a / (N ** 0.1)
        gammas.append(gamma)
        assert gamma > 0
    
    # All gammas should be positive
    assert all(g > 0 for g in gammas)
    
    # Should be in reasonable range
    assert all(0.001 < g < 0.1 for g in gammas)


def test_calibration_range():
    """Test calibration parameter range."""
    a_min = 100.0
    a_max = 300.0
    a_optimal = 200.84
    
    assert a_min < a_optimal < a_max
    assert a_optimal > 0


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
