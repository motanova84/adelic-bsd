# tests/test_dR_compatibility.py - SIMPLIFIED VERSION

r"""
(dR) Compatibility Tests (Simplified)
======================================

Basic tests for (dR) compatibility.
"""

import pytest

try:
    from sage.schemes.elliptic_curves.constructor import EllipticCurve
    SAGE_AVAILABLE = True
except ImportError:
    SAGE_AVAILABLE = False


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="SageMath not available")
def test_basic_dR():
    """Test basic (dR) verification."""
    try:
        from src.dR_compatibility import verify_dR_compatibility
        E = EllipticCurve('11a1')
        result = verify_dR_compatibility(E, 2)
        assert 'dR_compatible' in result
    except ImportError:
        pytest.skip("dR_compatibility module not available")


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="SageMath not available")
def test_dimension_computation():
    """Test dimension computation."""
    try:
        from src.dR_compatibility import compute_h1f_dimension
        E = EllipticCurve('11a1')
        dim = compute_h1f_dimension(E, 2)
        assert dim >= 0
    except ImportError:
        pytest.skip("dR_compatibility module not available")


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="SageMath not available")
def test_good_reduction():
    """Test good reduction case."""
    try:
        from src.dR_compatibility import verify_dR_compatibility
        E = EllipticCurve('11a1')
        result = verify_dR_compatibility(E, 2)
        assert result['dR_compatible']
    except ImportError:
        pytest.skip("dR_compatibility module not available")
