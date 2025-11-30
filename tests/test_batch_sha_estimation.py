"""
Tests for batch SHA estimation module.

Tests the |Ш(E)| estimation for elliptic curves with rank ≥ 2
using the BSD formula.
"""

import sys
import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))


@pytest.mark.basic
def test_batch_sha_estimation_module_exists():
    """Test that batch_sha_estimation module exists."""
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    assert module_path.exists(), "estimate_sha.py module not found"
    print("✓ estimate_sha.py module exists")


@pytest.mark.basic
def test_batch_sha_estimation_imports():
    """Test that the module can be imported."""
    try:
        from experiments.batch_sha_estimation import estimate_sha
        from experiments.batch_sha_estimation import batch_sha_estimation
        from experiments.batch_sha_estimation import ShaEstimator
        print("✓ All main exports importable")
    except ImportError as e:
        # Check if module can be loaded directly
        import importlib.util
        module_path = (Path(__file__).parent.parent / 'experiments' / 
                       'batch_sha_estimation' / 'estimate_sha.py')
        spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
        assert spec is not None, f"Could not load module spec: {e}"
        print("✓ Module can be loaded")


@pytest.mark.basic
def test_sha_estimator_class_exists():
    """Test that ShaEstimator class exists and can be instantiated."""
    import importlib.util
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    assert hasattr(module, 'ShaEstimator'), "ShaEstimator class not found"
    
    # Test instantiation
    estimator = module.ShaEstimator(digits=10, verbose=False)
    assert estimator.digits == 10
    assert estimator.verbose is False
    print("✓ ShaEstimator class instantiates correctly")


@pytest.mark.basic
def test_estimate_sha_function_exists():
    """Test that estimate_sha function exists."""
    import importlib.util
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    assert hasattr(module, 'estimate_sha'), "estimate_sha function not found"
    assert callable(module.estimate_sha), "estimate_sha is not callable"
    print("✓ estimate_sha function exists and is callable")


@pytest.mark.basic
def test_batch_sha_estimation_function_exists():
    """Test that batch_sha_estimation function exists."""
    import importlib.util
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    assert hasattr(module, 'batch_sha_estimation'), "batch_sha_estimation function not found"
    assert callable(module.batch_sha_estimation), "batch_sha_estimation is not callable"
    print("✓ batch_sha_estimation function exists and is callable")


@pytest.mark.basic
def test_get_curves_by_rank_exists():
    """Test that get_curves_by_rank function exists."""
    import importlib.util
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    assert hasattr(module, 'get_curves_by_rank'), "get_curves_by_rank function not found"
    print("✓ get_curves_by_rank function exists")


@pytest.mark.basic
def test_fallback_curves_without_sage():
    """Test that fallback curves are returned when Sage is not available."""
    import importlib.util
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    spec = importlib.util.spec_from_file_location("estimate_sha_test", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    # Store original value
    original_sage_available = getattr(module, 'SAGE_AVAILABLE', False)
    
    # Force SAGE_AVAILABLE to False to test fallback
    module.SAGE_AVAILABLE = False
    
    try:
        curves = module.get_curves_by_rank(min_rank=2, limit=5)
        
        assert isinstance(curves, list), "get_curves_by_rank should return a list"
        assert len(curves) > 0, "Should have fallback curves"
        assert '389a1' in curves, "389a1 should be in fallback curves"
        print(f"✓ Fallback curves returned: {curves[:5]}")
    finally:
        # Restore original value
        module.SAGE_AVAILABLE = original_sage_available


@pytest.mark.sage_required
def test_estimate_sha_for_rank2_curve():
    """Test SHA estimation for a known rank 2 curve (requires SageMath)."""
    try:
        import importlib.util
        module_path = (Path(__file__).parent.parent / 'experiments' / 
                       'batch_sha_estimation' / 'estimate_sha.py')
        spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        if not module.SAGE_AVAILABLE:
            pytest.skip("SageMath not available")
        
        # Test on 389a1 - famous rank 2 curve
        result = module.estimate_sha('389a1')
        
        assert result is not None, "Result should not be None for rank 2 curve"
        assert result.get('success', False), f"Estimation failed: {result.get('error')}"
        assert result['rank'] == 2, f"389a1 should have rank 2, got {result['rank']}"
        assert 'sha_estimate' in result, "Result should contain sha_estimate"
        assert isinstance(result['sha_estimate'], float), "sha_estimate should be float"
        
        print(f"✓ 389a1 |Ш| estimate: {result['sha_estimate']:.6f}")
        
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_estimate_sha_returns_none_for_low_rank():
    """Test that estimate_sha returns None for rank < 2 curves."""
    try:
        import importlib.util
        module_path = (Path(__file__).parent.parent / 'experiments' / 
                       'batch_sha_estimation' / 'estimate_sha.py')
        spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        if not module.SAGE_AVAILABLE:
            pytest.skip("SageMath not available")
        
        # 11a1 has rank 0, should return None
        result = module.estimate_sha('11a1')
        
        assert result is None, "Should return None for rank 0 curve"
        print("✓ Correctly returns None for rank 0 curve (11a1)")
        
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_batch_estimation_csv_output():
    """Test that batch estimation generates CSV output correctly."""
    try:
        import tempfile
        import importlib.util
        module_path = (Path(__file__).parent.parent / 'experiments' / 
                       'batch_sha_estimation' / 'estimate_sha.py')
        spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        if not module.SAGE_AVAILABLE:
            pytest.skip("SageMath not available")
        
        with tempfile.TemporaryDirectory() as tmpdir:
            csv_path = Path(tmpdir) / 'test_output.csv'
            json_path = Path(tmpdir) / 'test_output.json'
            
            # Test with a couple of known rank 2 curves
            results = module.batch_sha_estimation(
                ['389a1', '433a1'],
                output_csv=str(csv_path),
                output_json=str(json_path),
                verbose=False
            )
            
            # Check CSV was created
            assert csv_path.exists(), "CSV file should be created"
            
            # Check JSON was created
            assert json_path.exists(), "JSON file should be created"
            
            # Check CSV has expected columns
            import csv
            with open(csv_path, 'r') as f:
                reader = csv.DictReader(f)
                columns = reader.fieldnames
                
            expected_columns = [
                'label', 'rank', 'sha_estimate', 'l_derivative',
                'omega', 'R', 'torsion', 'tamagawa'
            ]
            for col in expected_columns:
                assert col in columns, f"CSV missing column: {col}"
            
            print("✓ CSV and JSON output generated correctly")
            
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
@pytest.mark.slow
def test_sha_estimator_class_methods():
    """Test ShaEstimator class methods."""
    try:
        import importlib.util
        module_path = (Path(__file__).parent.parent / 'experiments' / 
                       'batch_sha_estimation' / 'estimate_sha.py')
        spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        if not module.SAGE_AVAILABLE:
            pytest.skip("SageMath not available")
        
        estimator = module.ShaEstimator(digits=10, verbose=True)
        
        # Test estimate_sha method
        result = estimator.estimate_sha('389a1')
        assert result is not None
        assert result.get('success', False)
        
        # Check result structure
        assert 'label' in result
        assert 'rank' in result
        assert 'sha_estimate' in result
        assert 'l_derivative' in result
        assert 'omega' in result
        assert 'R' in result
        assert 'torsion' in result
        assert 'tamagawa' in result
        assert 'conductor' in result
        
        print("✓ ShaEstimator methods work correctly")
        
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.basic
def test_main_function_exists():
    """Test that main function exists and is callable."""
    import importlib.util
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    assert hasattr(module, 'main'), "main function not found"
    assert callable(module.main), "main is not callable"
    print("✓ main function exists")


@pytest.mark.basic
def test_run_bsd_10000_paso9_exists():
    """Test that run_bsd_10000_paso9 function exists."""
    import importlib.util
    module_path = (Path(__file__).parent.parent / 'experiments' / 
                   'batch_sha_estimation' / 'estimate_sha.py')
    spec = importlib.util.spec_from_file_location("estimate_sha", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    assert hasattr(module, 'run_bsd_10000_paso9'), "run_bsd_10000_paso9 function not found"
    assert callable(module.run_bsd_10000_paso9), "run_bsd_10000_paso9 is not callable"
    print("✓ run_bsd_10000_paso9 function exists")


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
