# Testing Guide

This directory contains tests for the Spectral Finiteness Framework.

## Test Files

- **`test_finiteness_basic.py`**: Basic structural tests that don't require SageMath
- **`test_finiteness.py`**: Full functional tests requiring SageMath

## Running Tests

### Basic Tests (No SageMath Required)

These tests verify package structure, documentation, and configuration:

```bash
python tests/test_finiteness_basic.py
```

Or with pytest:
```bash
pytest tests/test_finiteness_basic.py -v
```

### Full Tests (Requires SageMath)

These tests require SageMath to be installed:

```bash
# Using sage Python
sage -python tests/test_finiteness.py

# Or with pytest
sage -python -m pytest tests/test_finiteness.py -v
```

### All Tests

Run all tests with pytest:

```bash
# Basic tests only (no Sage)
pytest tests/test_finiteness_basic.py -v

# All tests (requires Sage)
sage -python -m pytest tests/ -v
```

## Continuous Integration

The GitHub Actions workflow runs basic tests automatically. For full tests with SageMath, the CI environment must have Sage installed via conda.

## Writing New Tests

### For Tests That Don't Require Sage

Add to `test_finiteness_basic.py`:

```python
def test_new_feature():
    """Test description"""
    # Test code here
    assert condition, "Error message"
    print("✓ Test passed")
```

### For Tests That Require Sage

Add to `test_finiteness.py`:

```python
def test_curve_analysis():
    """Test curve analysis"""
    from sage.all import EllipticCurve
    from src.spectral_finiteness import SpectralFinitenessProver
    
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()
    
    assert result['finiteness_proved'] == True
    print("✓ Test passed")
```

## Test Coverage

To check test coverage (requires SageMath and pytest-cov):

```bash
sage -python -m pytest --cov=src tests/ -v
```

## Troubleshooting

### "ModuleNotFoundError: No module named 'sage'"

This is expected if SageMath is not installed. Run basic tests only:
```bash
python tests/test_finiteness_basic.py
```

### Tests Fail in CI

- Check that environment.yml is correctly configured
- Ensure all dependencies are listed
- Verify Python version compatibility

### Import Errors

Make sure the package is installed or the path is set correctly:
```bash
pip install -e .
```

Or add to PYTHONPATH:
```bash
export PYTHONPATH="${PYTHONPATH}:$(pwd)"
```
