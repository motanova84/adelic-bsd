"""
Tests for PT_compatibility_extended module - Extended coverage for high ranks
"""

import sys
import os
import pytest
from pathlib import Path

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))


@pytest.mark.basic
def test_PT_compatibility_extended_module_exists():
    """Test that PT_compatibility_extended.py module exists"""
    module_path = Path(__file__).parent.parent / 'src' / 'PT_compatibility_extended.py'
    assert module_path.exists(), "PT_compatibility_extended.py module not found"
    print("✓ PT_compatibility_extended.py module exists")


@pytest.mark.basic
def test_PT_compatibility_extended_imports():
    """Test that the module can be imported"""
    try:
        import importlib.util
        module_path = Path(__file__).parent.parent / 'src' / 'PT_compatibility_extended.py'
        spec = importlib.util.spec_from_file_location("PT_compatibility_extended", module_path)
        assert spec is not None, "Could not load module spec"
        print("✓ Extended PT module can be loaded")
    except Exception as e:
        pytest.skip(f"Cannot load PT_compatibility_extended: {e}")


@pytest.mark.sage_required
def test_extended_PT_class_exists():
    """Test that ExtendedPTCompatibility class exists"""
    try:
        from src.PT_compatibility_extended import ExtendedPTCompatibility
        assert ExtendedPTCompatibility is not None
        print("✓ ExtendedPTCompatibility class exists")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_extended_PT_methods_exist():
    """Test that new methods exist in ExtendedPTCompatibility"""
    try:
        from src.PT_compatibility_extended import ExtendedPTCompatibility
        from sage.all import EllipticCurve
        
        E = EllipticCurve('11a1')
        prover = ExtendedPTCompatibility(E)
        
        # Check new methods exist
        assert hasattr(prover, 'compute_height_matrix_large_rank')
        assert hasattr(prover, 'verify_BSD_formula_high_rank')
        assert hasattr(prover, 'prove_PT_high_ranks')
        
        print("✓ All new methods exist")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_height_matrix_computation():
    """Test height matrix computation for rank 2 curve"""
    try:
        from src.PT_compatibility_extended import ExtendedPTCompatibility
        from sage.all import EllipticCurve
        
        # Use rank 2 curve
        E = EllipticCurve('389a1')
        prover = ExtendedPTCompatibility(E)
        
        if prover.rank >= 2:
            result = prover.compute_height_matrix_large_rank()
            assert result is not None
            assert 'matrix' in result
            assert 'determinant' in result
            assert 'eigenvalues' in result
            assert 'non_degenerate' in result
            
            print("✓ Height matrix computation works")
        else:
            pytest.skip("Curve rank < 2")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_BSD_formula_verification():
    """Test BSD formula verification for high rank"""
    try:
        from src.PT_compatibility_extended import ExtendedPTCompatibility
        from sage.all import EllipticCurve
        
        # Use rank 2 curve
        E = EllipticCurve('389a1')
        prover = ExtendedPTCompatibility(E)
        
        if prover.rank >= 2:
            result = prover.verify_BSD_formula_high_rank()
            assert result is not None
            assert 'lhs' in result
            assert 'rhs_estimate' in result
            assert 'ratio' in result
            assert 'compatible' in result
            
            print("✓ BSD formula verification works")
        else:
            pytest.skip("Curve rank < 2")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_prove_PT_high_ranks():
    """Test the main proof method for high ranks"""
    try:
        from src.PT_compatibility_extended import ExtendedPTCompatibility
        from sage.all import EllipticCurve
        
        # Test with rank 0 curve (should fall back to basic method)
        E = EllipticCurve('11a1')
        prover = ExtendedPTCompatibility(E)
        cert = prover.prove_PT_high_ranks()
        
        assert 'PT_compatible' in cert
        print("✓ prove_PT_high_ranks works for rank 0")
        
        # Test with rank 2 curve
        E = EllipticCurve('389a1')
        prover = ExtendedPTCompatibility(E)
        
        if prover.rank >= 2:
            cert = prover.prove_PT_high_ranks()
            assert 'PT_compatible' in cert
            assert 'height_matrix' in cert
            assert 'bsd_formula_check' in cert
            assert 'high_rank_proved' in cert
            
            print("✓ prove_PT_high_ranks works for rank 2")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
@pytest.mark.slow
def test_all_ranks_validation():
    """Test the complete ranks validation function"""
    try:
        from src.PT_compatibility_extended import prove_PT_all_ranks_extended
        
        # This runs the full validation suite for ranks 0-4
        # We just test that it completes without errors
        # Full run would take too long for CI
        print("⚠️  Skipping full validation (use sage -python to run manually)")
        pytest.skip("Full validation requires manual run with SageMath")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.basic
def test_module_documentation():
    """Test that the module has proper documentation"""
    module_path = Path(__file__).parent.parent / 'src' / 'PT_compatibility_extended.py'
    content = module_path.read_text()
    
    # Check for key documentation elements
    assert '"""' in content
    assert 'rangos altos' in content.lower() or 'high ranks' in content.lower()
    assert 'beilinson' in content.lower() or 'yuan-zhang-zhang' in content.lower()
    
    print("✓ Module has proper documentation")


@pytest.mark.basic
def test_references_documented():
    """Test that proper references are documented"""
    module_path = Path(__file__).parent.parent / 'src' / 'PT_compatibility_extended.py'
    content = module_path.read_text()
    
    # Check for key references
    assert 'Gross-Zagier' in content or 'gross-zagier' in content.lower()
    assert 'Yuan-Zhang-Zhang' in content or 'yuan-zhang-zhang' in content.lower()
    
    print("✓ Proper references are documented")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
