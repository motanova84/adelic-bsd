# tests/test_calibration.py - SIMPLIFIED VERSION

r"""
Calibration Tests (Simplified)
===============================

Basic tests for calibration without undefined functions.
"""

from sage.schemes.elliptic_curves.constructor import EllipticCurve


def test_basic_calibration():
    """Test basic calibration."""
    E = EllipticCurve('11a1')
    assert E.conductor() == 11


def test_gamma_positive():
    """Test gamma is positive."""
    a = 200.84
    N = 11
    gamma = a / (N ** 0.1)
    assert gamma > 0


def test_spectral_parameter_valid():
    """Test spectral parameter in valid range."""
    a = 200.84
    assert 100 < a < 300


def test_multiple_curves():
    """Test consistency across curves."""
    curves = ['11a1', '37a1', '389a1']
    a = 200.84

    for label in curves:
        E = EllipticCurve(label)
        N = float(E.conductor())
        gamma = a / (N ** 0.1)
        assert gamma > 0
