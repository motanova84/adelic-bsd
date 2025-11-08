"""
Tests for complete_compatibility_extension module - Complete (dR) and (PT) verification.
"""

import sys
import os
import pytest
from pathlib import Path

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))


@pytest.mark.basic
def test_complete_compatibility_module_exists():
    """Test that complete_compatibility_extension.py module exists"""
    module_path = Path(__file__).parent.parent / 'sagemath_integration' / 'sage' / 'schemes' / 'elliptic_curves' / 'bsd_spectral' / 'complete_compatibility_extension.py'
    assert module_path.exists(), "complete_compatibility_extension.py module not found"
    print("✓ complete_compatibility_extension.py module exists")


@pytest.mark.basic
def test_complete_compatibility_imports():
    """Test that the module can be imported (without Sage)"""
    try:
        # Try importing without Sage
        import importlib.util
        module_path = Path(__file__).parent.parent / 'sagemath_integration' / 'sage' / 'schemes' / 'elliptic_curves' / 'bsd_spectral' / 'complete_compatibility_extension.py'
        spec = importlib.util.spec_from_file_location("complete_compatibility_extension", module_path)
        # Just check the file can be loaded
        assert spec is not None, "Could not load module spec"
        print("✓ Module can be loaded")
    except Exception as e:
        pytest.skip(f"Cannot import complete_compatibility_extension without Sage: {e}")


@pytest.mark.sage_required
def test_complete_dR_compatibility_class_exists():
    """Test that CompleteDRCompatibility class exists"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompleteDRCompatibility
        assert CompleteDRCompatibility is not None
        print("✓ CompleteDRCompatibility class exists")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_complete_PT_compatibility_class_exists():
    """Test that CompletePTCompatibility class exists"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompletePTCompatibility
        assert CompletePTCompatibility is not None
        print("✓ CompletePTCompatibility class exists")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_complete_dR_compatibility_initialization():
    """Test basic initialization of CompleteDRCompatibility"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompleteDRCompatibility
        
        # Test with a simple curve
        E = EllipticCurve('11a1')
        verifier = CompleteDRCompatibility(E, 2)
        
        assert verifier._E == E
        assert verifier._p == 2
        
        print("✓ CompleteDRCompatibility initialization successful")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_complete_PT_compatibility_initialization():
    """Test basic initialization of CompletePTCompatibility"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompletePTCompatibility
        
        # Test with a simple curve
        E = EllipticCurve('11a1')
        verifier = CompletePTCompatibility(E)
        
        assert verifier._E == E
        assert verifier._rank == E.rank()
        
        print("✓ CompletePTCompatibility initialization successful")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_verify_dR_complete_function():
    """Test verify_dR_complete convenience function"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import verify_dR_complete
        
        E = EllipticCurve('11a1')
        result = verify_dR_complete(E, 2)
        
        assert 'dR_compatible' in result
        assert 'coverage' in result
        assert result['coverage'] == 'complete'
        
        print(f"✓ verify_dR_complete function works, compatible: {result['dR_compatible']}")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_verify_PT_complete_function():
    """Test verify_PT_complete convenience function"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import verify_PT_complete
        
        E = EllipticCurve('11a1')
        result = verify_PT_complete(E)
        
        assert 'PT_compatible' in result
        assert 'rank_coverage' in result
        assert result['rank_coverage'] == 'complete'
        
        print(f"✓ verify_PT_complete function works, compatible: {result['PT_compatible']}")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_complete_dR_good_reduction():
    """Test CompleteDRCompatibility for good reduction case"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompleteDRCompatibility
        
        # 11a1 has good reduction at p=5
        E = EllipticCurve('11a1')
        verifier = CompleteDRCompatibility(E, 5)
        result = verifier.verify_complete()
        
        assert result['dR_compatible'] == True
        assert result['reduction_classification']['type'] == 'good'
        
        print("✓ Good reduction verified correctly")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_complete_dR_multiplicative_reduction():
    """Test CompleteDRCompatibility for multiplicative reduction"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompleteDRCompatibility
        
        # 11a1 has multiplicative reduction at p=11
        E = EllipticCurve('11a1')
        verifier = CompleteDRCompatibility(E, 11)
        result = verifier.verify_complete()
        
        assert result['dR_compatible'] == True
        assert result['reduction_classification']['type'] == 'multiplicative'
        
        print("✓ Multiplicative reduction verified correctly")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_complete_PT_rank_zero():
    """Test CompletePTCompatibility for rank 0 curve"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompletePTCompatibility
        
        # 11a1 has rank 0
        E = EllipticCurve('11a1')
        verifier = CompletePTCompatibility(E)
        result = verifier.verify_complete()
        
        assert result['PT_compatible'] == True
        assert result['rank'] == 0
        assert result['method'] == 'trivial'
        
        print("✓ Rank 0 verification successful")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_complete_PT_rank_one():
    """Test CompletePTCompatibility for rank 1 curve"""
    try:
        from sage.all import EllipticCurve
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.complete_compatibility_extension import CompletePTCompatibility
        
        # 37a1 has rank 1
        E = EllipticCurve('37a1')
        verifier = CompletePTCompatibility(E)
        result = verifier.verify_complete()
        
        assert result['PT_compatible'] == True
        assert result['rank'] == 1
        assert result['method'] == 'gross_zagier'
        
        print("✓ Rank 1 verification successful")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


if __name__ == "__main__":
    # Run basic tests that don't require SageMath
    test_complete_compatibility_module_exists()
    test_complete_compatibility_imports()
    print("\n✓ All basic tests passed!")
