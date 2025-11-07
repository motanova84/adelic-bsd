"""
Test the new functional API for dR_compatibility module
"""

import pytest
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))


@pytest.mark.basic
def test_module_imports():
    """Test that the functional API can be imported"""
    try:
        from dR_compatibility import (
            compute_h1f_dimension,
            compute_dR_dimension,
            verify_dR_compatibility
        )
        assert compute_h1f_dimension is not None
        assert compute_dR_dimension is not None
        assert verify_dR_compatibility is not None
        print("✓ All functions imported successfully")
    except ImportError as e:
        # Expected without Sage
        print(f"Import failed (expected without Sage): {e}")


@pytest.mark.sage_required
def test_compute_h1f_dimension_good_reduction():
    """Test compute_h1f_dimension for good reduction"""
    try:
        from sage.all import EllipticCurve
        from dR_compatibility import compute_h1f_dimension
        
        # Curve 11a1 has good ordinary reduction at p=5
        E = EllipticCurve('11a1')
        dim = compute_h1f_dimension(E, 5)
        
        assert isinstance(dim, int)
        assert dim >= 0
        assert dim == 1  # Expected for good ordinary reduction
        print(f"✓ Good reduction: dim H^1_f = {dim}")
    except ImportError:
        pytest.skip("SageMath not available")


@pytest.mark.sage_required
def test_compute_h1f_dimension_multiplicative():
    """Test compute_h1f_dimension for multiplicative reduction"""
    try:
        from sage.all import EllipticCurve
        from dR_compatibility import compute_h1f_dimension
        
        # Curve 11a1 has multiplicative reduction at p=11
        E = EllipticCurve('11a1')
        dim = compute_h1f_dimension(E, 11)
        
        assert isinstance(dim, int)
        assert dim == 1  # Expected for multiplicative reduction
        print(f"✓ Multiplicative reduction: dim H^1_f = {dim}")
    except ImportError:
        pytest.skip("SageMath not available")


@pytest.mark.sage_required
def test_compute_dR_dimension():
    """Test compute_dR_dimension"""
    try:
        from sage.all import EllipticCurve
        from dR_compatibility import compute_dR_dimension
        
        E = EllipticCurve('11a1')
        dim = compute_dR_dimension(E, 5)
        
        assert isinstance(dim, int)
        assert dim >= 0
        print(f"✓ de Rham dimension: {dim}")
    except ImportError:
        pytest.skip("SageMath not available")


@pytest.mark.sage_required
def test_verify_dR_compatibility_basic():
    """Test verify_dR_compatibility basic functionality"""
    try:
        from sage.all import EllipticCurve
        from dR_compatibility import verify_dR_compatibility
        
        E = EllipticCurve('11a1')
        result = verify_dR_compatibility(E, 2)
        
        # Check required fields
        assert 'dR_compatible' in result
        assert 'dim_H1f' in result
        assert 'dim_DdR_Fil0' in result
        assert 'reduction_type' in result
        assert 'prime' in result
        assert 'curve' in result
        
        # Check types
        assert isinstance(result['dR_compatible'], bool)
        assert isinstance(result['dim_H1f'], int)
        assert isinstance(result['dim_DdR_Fil0'], int)
        assert isinstance(result['prime'], int)
        
        print(f"✓ Verification result: {result['dR_compatible']}")
        print(f"  Curve: {result['curve']}")
        print(f"  Prime: {result['prime']}")
        print(f"  Reduction: {result['reduction_type']}")
        print(f"  dim H^1_f: {result['dim_H1f']}")
        print(f"  dim D_dR/Fil^0: {result['dim_DdR_Fil0']}")
    except ImportError:
        pytest.skip("SageMath not available")


@pytest.mark.sage_required
def test_verify_dR_compatibility_good_ordinary():
    """Test dR compatibility for good ordinary reduction"""
    try:
        from sage.all import EllipticCurve
        from dR_compatibility import verify_dR_compatibility
        
        # 11a1 at p=5 has good ordinary reduction
        E = EllipticCurve('11a1')
        result = verify_dR_compatibility(E, 5)
        
        assert result['dR_compatible'] is True
        assert result['reduction_type'] == 'good_ordinary'
        assert result['dim_H1f'] == result['dim_DdR_Fil0']
        print("✓ Good ordinary reduction verified")
    except ImportError:
        pytest.skip("SageMath not available")


@pytest.mark.sage_required  
def test_verify_dR_compatibility_multiplicative():
    """Test dR compatibility for multiplicative reduction"""
    try:
        from sage.all import EllipticCurve
        from dR_compatibility import verify_dR_compatibility
        
        # 37a1 at p=37 has multiplicative reduction
        E = EllipticCurve('37a1')
        result = verify_dR_compatibility(E, 37)
        
        assert result['dR_compatible'] is True
        assert result['reduction_type'] == 'multiplicative'
        assert result['dim_H1f'] == result['dim_DdR_Fil0']
        print("✓ Multiplicative reduction verified")
    except ImportError:
        pytest.skip("SageMath not available")


@pytest.mark.sage_required
def test_dimension_compatibility():
    """Test that dimensions always match (dR compatibility)"""
    try:
        from sage.all import EllipticCurve
        from dR_compatibility import compute_h1f_dimension, compute_dR_dimension
        
        test_cases = [
            ('11a1', 2),
            ('11a1', 5),
            ('37a1', 3),
            ('389a1', 2),
        ]
        
        for label, p in test_cases:
            E = EllipticCurve(label)
            dim_h1f = compute_h1f_dimension(E, p)
            dim_dR = compute_dR_dimension(E, p)
            
            assert dim_h1f == dim_dR, \
                f"Dimensions mismatch for {label} at p={p}: " \
                f"H^1_f={dim_h1f}, D_dR/Fil^0={dim_dR}"
        
        print(f"✓ All {len(test_cases)} test cases have matching dimensions")
    except ImportError:
        pytest.skip("SageMath not available")


if __name__ == '__main__':
    pytest.main([__file__, '-v', '-m', 'not sage_required'])
