"""
Tests for sha_empirical_estimator module - BSD ∞³ Sha estimation validation.

Tests the empirical Sha estimation functionality for elliptic curves
with rank >= 2.
"""

import sys
import os
import pytest
from pathlib import Path
import tempfile
import shutil
import importlib.util

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


def _import_sha_estimator():
    """Helper function to directly import sha_empirical_estimator module."""
    module_path = Path(__file__).parent.parent / 'src' / 'verification' / 'sha_empirical_estimator.py'
    spec = importlib.util.spec_from_file_location("sha_empirical_estimator", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.mark.basic
def test_sha_estimator_module_exists():
    """Test that sha_empirical_estimator.py module exists."""
    module_path = Path(__file__).parent.parent / 'src' / 'verification' / 'sha_empirical_estimator.py'
    assert module_path.exists(), "sha_empirical_estimator.py module not found"
    print("✓ sha_empirical_estimator.py module exists")


@pytest.mark.basic
def test_sha_estimator_imports():
    """Test that the module can be imported."""
    try:
        module = _import_sha_estimator()
        assert hasattr(module, 'ShaEmpiricalEstimator')
        assert hasattr(module, 'run_empirical_validation')
        assert hasattr(module, 'estimate_sha_dataframe')
        print("✓ Module imports successfully")
    except ImportError as e:
        pytest.fail(f"Failed to import sha_empirical_estimator: {e}")


@pytest.mark.basic
def test_sha_estimator_initialization():
    """Test that ShaEmpiricalEstimator can be initialized with default parameters."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator = ShaEmpiricalEstimator()
    assert estimator.num_curves == 500
    assert estimator.start_index == 10001
    assert estimator.random_seed is None
    print("✓ ShaEmpiricalEstimator initializes with default parameters")


@pytest.mark.basic
def test_sha_estimator_custom_initialization():
    """Test that ShaEmpiricalEstimator can be initialized with custom parameters."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator = ShaEmpiricalEstimator(
        num_curves=100,
        start_index=20001,
        random_seed=42
    )
    assert estimator.num_curves == 100
    assert estimator.start_index == 20001
    assert estimator.random_seed == 42
    print("✓ ShaEmpiricalEstimator initializes with custom parameters")


@pytest.mark.basic
def test_generate_simulation():
    """Test that generate_simulation produces a valid DataFrame."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    import pandas as pd
    
    estimator = ShaEmpiricalEstimator(num_curves=10, random_seed=42)
    df = estimator.generate_simulation()
    
    # Check DataFrame structure
    assert isinstance(df, pd.DataFrame)
    assert len(df) == 10
    
    # Check required columns
    required_columns = [
        "CurveID", "Conductor", "Rank", "TorsionOrder",
        "Regulator", "RealPeriod", "L'(E,1)", "ShaEstimate"
    ]
    for col in required_columns:
        assert col in df.columns, f"Missing column: {col}"
    
    print("✓ generate_simulation produces valid DataFrame")


@pytest.mark.basic
def test_curve_ids_format():
    """Test that curve IDs are generated in the correct format."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator = ShaEmpiricalEstimator(num_curves=5, start_index=10001, random_seed=42)
    df = estimator.generate_simulation()
    
    expected_ids = ["E_10001", "E_10002", "E_10003", "E_10004", "E_10005"]
    actual_ids = df["CurveID"].tolist()
    
    assert actual_ids == expected_ids
    print("✓ Curve IDs are generated correctly")


@pytest.mark.basic
def test_ranks_are_geq_2():
    """Test that all generated ranks are >= 2."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator = ShaEmpiricalEstimator(num_curves=100, random_seed=42)
    df = estimator.generate_simulation()
    
    assert (df["Rank"] >= 2).all(), "All ranks should be >= 2"
    assert set(df["Rank"].unique()).issubset({2, 3, 4}), "Ranks should be in {2, 3, 4}"
    print("✓ All ranks are >= 2")


@pytest.mark.basic
def test_sha_estimate_formula():
    """Test that Sha estimate is computed correctly."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    import numpy as np
    
    estimator = ShaEmpiricalEstimator()
    
    # Test with known values
    l_deriv = 0.5
    torsion = 2
    regulator = 1.0
    period = 2.0
    
    # Expected: (0.5 * 4) / (1.0 * 2.0) = 1.0
    expected = (l_deriv * torsion**2) / (regulator * period)
    actual = estimator.estimate_sha(l_deriv, torsion, regulator, period)
    
    assert abs(actual - expected) < 0.001, f"Expected {expected}, got {actual}"
    print("✓ Sha estimate formula is correct")


@pytest.mark.basic
def test_sha_estimate_array():
    """Test that Sha estimate works with numpy arrays."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    import numpy as np
    
    estimator = ShaEmpiricalEstimator()
    
    l_deriv = np.array([0.5, 1.0])
    torsion = np.array([2, 3])
    regulator = np.array([1.0, 2.0])
    period = np.array([2.0, 1.0])
    
    result = estimator.estimate_sha(l_deriv, torsion, regulator, period)
    
    assert len(result) == 2
    assert isinstance(result, np.ndarray)
    print("✓ Sha estimate works with arrays")


@pytest.mark.basic
def test_get_statistics():
    """Test that get_statistics returns expected structure."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator = ShaEmpiricalEstimator(num_curves=50, random_seed=42)
    estimator.generate_simulation()
    stats = estimator.get_statistics()
    
    # Check required keys
    required_keys = [
        "total_curves", "rank_distribution", "sha_statistics",
        "regulator_statistics", "period_statistics",
        "curves_with_sha_gt_1", "curves_with_sha_square"
    ]
    for key in required_keys:
        assert key in stats, f"Missing key: {key}"
    
    # Check sha_statistics structure
    sha_stats_keys = ["mean", "std", "min", "max", "median"]
    for key in sha_stats_keys:
        assert key in stats["sha_statistics"], f"Missing sha_statistics key: {key}"
    
    assert stats["total_curves"] == 50
    print("✓ get_statistics returns expected structure")


@pytest.mark.basic
def test_get_by_rank():
    """Test filtering results by rank."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator = ShaEmpiricalEstimator(num_curves=100, random_seed=42)
    estimator.generate_simulation()
    
    rank_2_curves = estimator.get_by_rank(2)
    rank_3_curves = estimator.get_by_rank(3)
    
    assert (rank_2_curves["Rank"] == 2).all()
    assert (rank_3_curves["Rank"] == 3).all()
    print("✓ get_by_rank filters correctly")


@pytest.mark.basic
def test_reproducibility():
    """Test that results are reproducible with the same seed."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator1 = ShaEmpiricalEstimator(num_curves=20, random_seed=42)
    df1 = estimator1.generate_simulation()
    
    estimator2 = ShaEmpiricalEstimator(num_curves=20, random_seed=42)
    df2 = estimator2.generate_simulation()
    
    # Compare DataFrames
    assert df1.equals(df2), "Results should be identical with the same seed"
    print("✓ Results are reproducible with same seed")


@pytest.mark.basic
def test_generate_certificate():
    """Test that generate_certificate returns valid structure."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    
    estimator = ShaEmpiricalEstimator(num_curves=10, random_seed=42)
    estimator.generate_simulation()
    certificate = estimator.generate_certificate()
    
    # Check required keys
    required_keys = [
        "certificate_id", "protocol", "module", "timestamp",
        "simulation_parameters", "statistics", "verification_status", "framework"
    ]
    for key in required_keys:
        assert key in certificate, f"Missing key: {key}"
    
    assert certificate["protocol"] == "SABIO_∞³"
    assert certificate["module"] == "sha_empirical_estimator"
    assert certificate["verification_status"] == "completed"
    print("✓ generate_certificate returns valid structure")


@pytest.mark.basic
def test_export_to_csv():
    """Test CSV export functionality."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    import pandas as pd
    
    estimator = ShaEmpiricalEstimator(num_curves=10, random_seed=42)
    estimator.generate_simulation()
    
    with tempfile.TemporaryDirectory() as tmpdir:
        output_path = Path(tmpdir) / "test_sha.csv"
        result_path = estimator.export_to_csv(output_path)
        
        assert result_path.exists()
        
        # Verify CSV content
        df_loaded = pd.read_csv(result_path)
        assert len(df_loaded) == 10
        assert "CurveID" in df_loaded.columns
        assert "ShaEstimate" in df_loaded.columns
    
    print("✓ CSV export works correctly")


@pytest.mark.basic
def test_export_to_json():
    """Test JSON export functionality."""
    module = _import_sha_estimator()
    ShaEmpiricalEstimator = module.ShaEmpiricalEstimator
    import json
    
    estimator = ShaEmpiricalEstimator(num_curves=10, random_seed=42)
    estimator.generate_simulation()
    
    with tempfile.TemporaryDirectory() as tmpdir:
        output_path = Path(tmpdir) / "test_sha.json"
        result_path = estimator.export_to_json(output_path)
        
        assert result_path.exists()
        
        # Verify JSON content
        with open(result_path) as f:
            data = json.load(f)
        
        assert "metadata" in data
        assert "statistics" in data
        assert "curves" in data
        assert len(data["curves"]) == 10
    
    print("✓ JSON export works correctly")


@pytest.mark.basic
def test_run_empirical_validation():
    """Test the run_empirical_validation convenience function."""
    module = _import_sha_estimator()
    run_empirical_validation = module.run_empirical_validation
    
    results = run_empirical_validation(
        num_curves=20,
        start_index=10001,
        random_seed=42,
        verbose=False
    )
    
    assert "dataframe" in results
    assert "statistics" in results
    assert "certificate" in results
    assert "estimator" in results
    
    assert len(results["dataframe"]) == 20
    print("✓ run_empirical_validation works correctly")


@pytest.mark.basic
def test_estimate_sha_dataframe():
    """Test the estimate_sha_dataframe convenience function."""
    module = _import_sha_estimator()
    estimate_sha_dataframe = module.estimate_sha_dataframe
    import pandas as pd
    
    df = estimate_sha_dataframe(num_curves=30, start_index=10001, random_seed=42)
    
    assert isinstance(df, pd.DataFrame)
    assert len(df) == 30
    assert df["CurveID"].iloc[0] == "E_10001"
    print("✓ estimate_sha_dataframe works correctly")


@pytest.mark.basic
def test_module_from_init():
    """Test that module is properly exported from verification __init__.py."""
    # This test checks if the __init__.py is properly updated
    # but may skip if sage is not available
    try:
        from src.verification import (
            ShaEmpiricalEstimator,
            run_empirical_validation,
            estimate_sha_dataframe
        )
        assert ShaEmpiricalEstimator is not None
        assert run_empirical_validation is not None
        assert estimate_sha_dataframe is not None
        print("✓ Module exported correctly from __init__.py")
    except ImportError as e:
        if "sage" in str(e).lower():
            pytest.skip(f"SageMath not available, skipping __init__ test: {e}")
        else:
            pytest.fail(f"Failed to import from verification module: {e}")


@pytest.mark.basic
def test_run_with_output_dir():
    """Test run_empirical_validation with output directory."""
    module = _import_sha_estimator()
    run_empirical_validation = module.run_empirical_validation
    
    with tempfile.TemporaryDirectory() as tmpdir:
        results = run_empirical_validation(
            num_curves=10,
            random_seed=42,
            output_dir=tmpdir,
            verbose=False
        )
        
        output_path = Path(tmpdir)
        assert (output_path / "sha_estimates.csv").exists()
        assert (output_path / "sha_validation.json").exists()
        assert (output_path / "sha_validation_certificate.json").exists()
    
    print("✓ Output files are created correctly")


@pytest.mark.basic
def test_problem_statement_scenario():
    """Test the exact scenario from the problem statement."""
    module = _import_sha_estimator()
    estimate_sha_dataframe = module.estimate_sha_dataframe
    
    # Problem statement: 500 curves E_10001 to E_10500
    df = estimate_sha_dataframe(num_curves=500, start_index=10001, random_seed=42)
    
    # Verify structure matches problem statement
    assert len(df) == 500
    assert df["CurveID"].iloc[0] == "E_10001"
    assert df["CurveID"].iloc[-1] == "E_10500"
    
    # Verify all ranks are >= 2
    assert (df["Rank"] >= 2).all()
    
    # Verify column structure
    expected_columns = [
        "CurveID", "Conductor", "Rank", "TorsionOrder",
        "Regulator", "RealPeriod", "L'(E,1)", "ShaEstimate"
    ]
    assert list(df.columns) == expected_columns
    
    print("✓ Problem statement scenario passes")
    print(f"  Generated {len(df)} curves from E_10001 to E_10500")
    print(f"  Rank distribution: {df['Rank'].value_counts().to_dict()}")


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
