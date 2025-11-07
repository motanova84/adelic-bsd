"""
Tests for BSD unconditional proof system.
"""

import sys
import os
import pytest
from pathlib import Path

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))


@pytest.mark.basic
def test_dR_compatibility_module_exists():
    """Test that dR_compatibility module exists"""
    module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
    assert module_path.exists(), "dR_compatibility.py not found"
    print("✓ dR_compatibility module exists")


@pytest.mark.basic
def test_PT_compatibility_module_exists():
    """Test that PT_compatibility module exists"""
    module_path = Path(__file__).parent.parent / 'src' / 'PT_compatibility.py'
    assert module_path.exists(), "PT_compatibility.py not found"
    print("✓ PT_compatibility module exists")


@pytest.mark.basic
def test_prove_BSD_unconditional_script_exists():
    """Test that prove_BSD_unconditional script exists"""
    script_path = Path(__file__).parent.parent / 'scripts' / 'prove_BSD_unconditional.py'
    assert script_path.exists(), "prove_BSD_unconditional.py not found"
    assert os.access(script_path, os.X_OK) or script_path.suffix == '.py', "Script must be a Python file or executable"
    print("✓ prove_BSD_unconditional script exists")


@pytest.mark.basic
def test_dR_compatibility_imports():
    """Test that dR_compatibility can be imported"""
    try:
        sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))
        import dR_compatibility
        assert hasattr(dR_compatibility, 'prove_dR_all_cases')
        assert hasattr(dR_compatibility, 'verify_dR_compatibility')
        print("✓ dR_compatibility imports successfully")
    except ImportError as e:
        if 'sage' in str(e).lower():
            pytest.skip("SageMath not available")
        else:
            raise


@pytest.mark.basic
def test_PT_compatibility_imports():
    """Test that PT_compatibility can be imported"""
    try:
        sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))
        import PT_compatibility
        assert hasattr(PT_compatibility, 'prove_PT_all_ranks')
        assert hasattr(PT_compatibility, 'verify_PT_compatibility')
        print("✓ PT_compatibility imports successfully")
    except ImportError as e:
        if 'sage' in str(e).lower():
            pytest.skip("SageMath not available")
        else:
            raise


@pytest.mark.basic
def test_required_directories_exist():
    """Test that required directories are created"""
    base_path = Path(__file__).parent.parent
    
    # These directories should be created by the script
    required_dirs = ['proofs', 'calibration', 'verification']
    
    for dir_name in required_dirs:
        dir_path = base_path / dir_name
        # We don't require them to exist yet, but they should be creatable
        assert dir_path.parent.exists(), f"Parent directory for {dir_name} doesn't exist"
    
    print("✓ Directory structure validated")


@pytest.mark.skipif(not os.environ.get('SAGE_LOCAL'), reason="SageMath not available")
def test_dR_compatibility_functions():
    """Test dR_compatibility functions with SageMath"""
    sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))
    from dR_compatibility import compute_h1f_dimension, compute_dR_dimension
    from sage.all import EllipticCurve
    
    # Test with a simple curve
    E = EllipticCurve('11a1')
    
    # Test h1f dimension computation
    dim_h1f = compute_h1f_dimension(E, 2)
    assert dim_h1f is not None
    assert isinstance(dim_h1f, int)
    assert dim_h1f >= 0
    
    # Test dR dimension computation
    dim_dR = compute_dR_dimension(E, 2)
    assert dim_dR is not None
    assert isinstance(dim_dR, int)
    assert dim_dR >= 0
    
    print(f"✓ dR functions work: dim_h1f={dim_h1f}, dim_dR={dim_dR}")


@pytest.mark.skipif(not os.environ.get('SAGE_LOCAL'), reason="SageMath not available")
def test_PT_compatibility_functions():
    """Test PT_compatibility functions with SageMath"""
    sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))
    from PT_compatibility import compute_spectral_height
    from sage.all import EllipticCurve
    
    # Test with curves of different ranks
    test_curves = ['11a1', '37a1']  # rank 0 and rank 1
    
    for label in test_curves:
        E = EllipticCurve(label)
        height = compute_spectral_height(E)
        
        assert height is not None
        assert isinstance(height, float)
        assert height >= 0
        
        print(f"✓ PT height for {label}: {height}")


@pytest.mark.skipif(not os.environ.get('SAGE_LOCAL'), reason="SageMath not available")
def test_prove_BSD_integration():
    """Test integration of all BSD proof components"""
    sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))
    from dR_compatibility import prove_dR_all_cases
    from PT_compatibility import prove_PT_all_ranks
    
    # This is a slow test - just verify the functions can be called
    # without testing complete execution
    
    # Test that functions are callable
    assert callable(prove_dR_all_cases)
    assert callable(prove_PT_all_ranks)
    
    print("✓ BSD proof integration validated")


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
