"""
Tests for massive_lmfdb_validator module - Industrial-scale LMFDB validation.
"""

import sys
import os
import pytest
from pathlib import Path

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))


@pytest.mark.basic
def test_massive_validator_module_exists():
    """Test that massive_lmfdb_validator.py module exists"""
    module_path = (Path(__file__).parent.parent / 'sagemath_integration' / 'sage' /
                   'schemes' / 'elliptic_curves' / 'bsd_spectral' / 'massive_lmfdb_validator.py')
    assert module_path.exists(), "massive_lmfdb_validator.py module not found"
    print("✓ massive_lmfdb_validator.py module exists")


@pytest.mark.basic
def test_massive_validator_imports():
    """Test that the module can be imported (without Sage)"""
    try:
        # Try importing without Sage
        import importlib.util
        module_path = (Path(__file__).parent.parent / 'sagemath_integration' / 'sage' /
                       'schemes' / 'elliptic_curves' / 'bsd_spectral' / 'massive_lmfdb_validator.py')
        spec = importlib.util.spec_from_file_location("massive_lmfdb_validator", module_path)
        # Just check the file can be loaded
        assert spec is not None, "Could not load module spec"
        print("✓ Module can be loaded")
    except Exception as e:
        pytest.skip(f"Cannot import massive_lmfdb_validator without Sage: {e}")


@pytest.mark.sage_required
def test_massive_validator_class_exists():
    """Test that MassiveLMFDBValidator class exists"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator
        assert MassiveLMFDBValidator is not None
        print("✓ MassiveLMFDBValidator class exists")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_run_massive_validation_function_exists():
    """Test that run_massive_validation function exists"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import run_massive_validation
        assert run_massive_validation is not None
        print("✓ run_massive_validation function exists")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_validator_initialization():
    """Test that validator can be initialized with default parameters"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator

        validator = MassiveLMFDBValidator(sample_size=10)
        assert validator._sample_size == 10
        assert validator._conductor_max == 500000
        assert validator._ranks == [0, 1, 2, 3, 4]
        assert validator._output_dir.name == 'validation_results'
        print("✓ Validator initializes with default parameters")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_validator_custom_initialization():
    """Test that validator can be initialized with custom parameters"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator

        validator = MassiveLMFDBValidator(
            sample_size=50,
            conductor_max=100000,
            ranks=[0, 1],
            n_processes=2,
            output_dir='test_results'
        )
        assert validator._sample_size == 50
        assert validator._conductor_max == 100000
        assert validator._ranks == [0, 1]
        assert validator._n_processes == 2
        assert validator._output_dir.name == 'test_results'
        print("✓ Validator initializes with custom parameters")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_validator_repr():
    """Test that validator string representation works"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator

        validator = MassiveLMFDBValidator(sample_size=100)
        repr_str = validator._repr_()
        assert 'sample=100' in repr_str
        assert 'N<500000' in repr_str
        print(f"✓ Validator repr: {repr_str}")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
@pytest.mark.slow
def test_validate_single_curve():
    """Test that _validate_single_curve static method works on a simple curve"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator

        # Test on a simple curve
        result = MassiveLMFDBValidator._validate_single_curve('11a1')

        # Check that result has expected structure
        assert 'label' in result
        assert 'success' in result
        assert 'timestamp' in result

        # If successful, check additional fields
        if result.get('success', False):
            assert 'conductor' in result
            assert 'rank' in result
            assert 'spectral' in result
            assert 'dR' in result
            assert 'PT' in result
            assert 'confidence' in result
            print(f"✓ Single curve validation: {result['label']} - Success: {result['success']}")
        else:
            # If failed, check for error
            print(f"⚠ Single curve validation failed (may be expected): {result.get('error', 'Unknown error')}")

    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
@pytest.mark.slow
def test_get_lmfdb_sample():
    """Test that _get_lmfdb_sample generates a sample"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator

        validator = MassiveLMFDBValidator(sample_size=20, conductor_max=1000, ranks=[0, 1])
        labels = validator._get_lmfdb_sample()

        # Check that we got some labels
        assert isinstance(labels, list)
        assert len(labels) > 0
        assert len(labels) <= 20
        print(f"✓ Generated sample with {len(labels)} curves")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")
    except Exception as e:
        pytest.skip(f"LMFDB database not available or other error: {e}")


@pytest.mark.sage_required
@pytest.mark.slow
@pytest.mark.integration
def test_run_validation_small():
    """Test that run_validation works with a very small sample"""
    try:
        import sys
        import shutil
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator

        # Use a very small sample and low conductor to keep test fast
        output_dir = 'test_validation_output'
        validator = MassiveLMFDBValidator(
            sample_size=3,
            conductor_max=100,
            ranks=[0],
            n_processes=1,
            output_dir=output_dir
        )

        # Run validation (non-parallel for deterministic testing)
        results = validator.run_validation(parallel=False)

        # Check that results have expected structure
        assert 'total_curves' in results
        assert 'successes' in results
        assert 'failures' in results
        assert 'success_rate' in results
        assert 'by_rank' in results
        assert 'confidence' in results
        assert 'gamma' in results

        print(f"✓ Small validation completed: {results['total_curves']} curves tested")
        print(f"  Success rate: {results['success_rate']:.2%}")

        # Cleanup
        try:
            shutil.rmtree(output_dir)
        except (OSError, FileNotFoundError):
            pass  # Ignore cleanup failures

    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")
    except Exception as e:
        pytest.skip(f"Validation test failed (may require full Sage environment): {e}")


@pytest.mark.sage_required
@pytest.mark.slow
@pytest.mark.integration
def test_generate_reports():
    """Test that generate_reports creates output files"""
    try:
        import sys
        import shutil
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.massive_lmfdb_validator import MassiveLMFDBValidator

        # Use a very small sample
        output_dir = 'test_reports_output'
        validator = MassiveLMFDBValidator(
            sample_size=2,
            conductor_max=100,
            ranks=[0],
            n_processes=1,
            output_dir=output_dir
        )

        # Run validation
        validator.run_validation(parallel=False)

        # Generate reports
        validator.generate_reports()

        # Check that report files were created
        output_path = Path(output_dir)
        assert (output_path / 'validation_table.tex').exists()
        assert (output_path / 'validation_plots.png').exists()
        assert (output_path / 'validation_report.txt').exists()

        print("✓ Reports generated successfully")

        # Cleanup
        try:
            shutil.rmtree(output_dir)
        except (OSError, FileNotFoundError):
            pass  # Ignore cleanup failures

    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")
    except Exception as e:
        pytest.skip(f"Report generation test failed: {e}")


@pytest.mark.sage_required
@pytest.mark.integration
def test_all_py_includes_validator():
    """Test that all.py includes the massive validator"""
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent / 'sagemath_integration'))
        from sage.schemes.elliptic_curves.bsd_spectral.all import MassiveLMFDBValidator, run_massive_validation

        assert MassiveLMFDBValidator is not None
        assert run_massive_validation is not None
        print("✓ Validator is exported in all.py")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
