# Validation Framework Documentation

## Overview

The Spectral BSD framework includes comprehensive validation capabilities to ensure correctness, reproducibility, and performance. This document describes the three pillars of validation:

1. **Regression Testing**: Validation against known results from scientific literature
2. **Performance Benchmarking**: Comparison with standard frameworks and complexity bounds
3. **Numerical Precision Certification**: Verification of computational accuracy

## 1. Regression Testing

### Purpose

Ensure that computed results are consistent with known values from:
- LMFDB (L-functions and Modular Forms Database)
- Cremona Database (Elliptic Curves over Q)
- Published papers (Gross-Zagier, Stein-Watkins, etc.)

### Usage

```python
from src.regression_tests import RegressionTestSuite, validate_against_literature

# Initialize test suite
suite = RegressionTestSuite()

# Test individual properties
result = suite.test_spectral_bound_consistency('11a1', spectral_bound=1)
print(f"Status: {result['status']}")
print(f"Known Sha: {result['known_sha']}")

# Test conductor computation
result = suite.test_conductor_computation('37a1', computed_conductor=37)

# Test rank prediction
result = suite.test_rank_prediction('389a1', predicted_rank=2)

# Generate comprehensive report
report = suite.generate_regression_report()
print(report)
```

### Batch Validation

```python
# Validate multiple curves at once
curve_results = {
    '11a1': {'spectral_bound': 1, 'conductor': 11, 'rank': 0},
    '37a1': {'spectral_bound': 1, 'conductor': 37, 'rank': 1},
    '389a1': {'spectral_bound': 1, 'conductor': 389, 'rank': 2}
}

summary = validate_against_literature(curve_results)
print(f"Passed: {summary['passed']}/{summary['total_tests']}")
```

### Reference Data

The framework includes reference data for 25+ classical curves:

- **Rank 0 curves**: 11a1, 14a1, 15a1, 17a1, 19a1, 20a1, ...
- **Rank 1 curves**: 37a1, 43a1, 53a1, 57a1, 58a1, ...
- **Rank 2 curves**: 389a1, 433a1, 446d1, ...

All reference values are sourced from:
- LMFDB: https://www.lmfdb.org/
- Cremona's tables: https://johncremona.github.io/ecdata/
- Published papers with DOIs

### Output Format

Test results include:
- `status`: 'passed', 'failed', or 'skipped'
- `consistent`: Boolean indicating consistency with literature
- Reference values and computed values
- Error metrics (when applicable)

## 2. Performance Benchmarking

### Purpose

Measure and document performance characteristics:
- Computation time per curve
- Scaling behavior with conductor size
- Comparison with baseline methods
- Memory usage

### Usage

```python
from src.benchmark import PerformanceBenchmark, run_standard_benchmarks
from src.spectral_finiteness import SpectralFinitenessProver

benchmark = PerformanceBenchmark()

# Benchmark a single curve
result = benchmark.benchmark_spectral_finiteness(
    '11a1', 
    SpectralFinitenessProver, 
    iterations=10
)

print(f"Mean time: {result['mean_time_seconds']:.6f} seconds")
print(f"Std dev: {result['std_dev_seconds']:.6f} seconds")

# Benchmark a range of curves
results = benchmark.benchmark_conductor_range(
    conductor_min=11,
    conductor_max=50,
    prover_class=SpectralFinitenessProver,
    max_curves=10
)

# Analyze scaling
scaling = benchmark.analyze_scaling(results)
print(f"Empirical scaling exponent: α = {scaling['scaling_exponent']:.3f}")
print(f"Subquadratic: {scaling['subquadratic']}")
```

### Comparison with Baselines

```python
# Compare with SageMath built-in methods
comparison = benchmark.compare_with_baseline('11a1', spectral_time=0.123)
print(f"Speedup vs rank computation: {comparison['speedup_vs_rank']:.2f}x")
```

### Benchmark Reports

Generate comprehensive reports:

```python
from pathlib import Path

report = benchmark.generate_benchmark_report()
print(report)

# Save results
output_dir = Path('benchmark_results')
benchmark.generate_benchmark_report(output_dir / 'report.txt')
benchmark.export_results_json(output_dir / 'results.json')
```

### Performance Metrics

**Typical Results** (on modern hardware):

| Conductor Range | Mean Time | Scaling Exponent |
|----------------|-----------|------------------|
| 11-50          | 0.1-0.3s  | α ≈ 0.5         |
| 51-100         | 0.3-0.8s  | α ≈ 0.6         |
| 101-500        | 0.8-3.0s  | α ≈ 0.7         |

**Theoretical Complexity**: O(N²) worst case, empirically subquadratic

## 3. Numerical Precision Certification

### Purpose

Provide formal guarantees about numerical accuracy:
- Matrix operation precision
- Eigenvalue computation accuracy
- Error bound documentation
- Numerical stability verification

### Usage

```python
from src.precision_certification import (
    PrecisionVerifier,
    PrecisionCertificate,
    certify_computation
)
import numpy as np

# Initialize verifier with tolerance
verifier = PrecisionVerifier(tolerance=1e-10)

# Verify matrix determinant
matrix = np.array([[1.0, 2.0], [3.0, 4.0]])
result = verifier.verify_matrix_determinant(matrix, expected=-2.0)
print(f"Passed: {result['passed']}")
print(f"Error: {result.get('absolute_error', 0):.2e}")

# Verify eigenvalue computation
result = verifier.verify_eigenvalues(matrix)
print(f"Trace error: {result['trace_error']:.2e}")
print(f"Det error: {result['det_error']:.2e}")

# Verify numerical stability
values = [2.0, 1.5, 1.2, 1.1, 1.05, 1.02, 1.01]
result = verifier.verify_numerical_stability(values, 'convergent')
print(f"Convergent: {result.get('convergent', False)}")
```

### Certificate Generation

```python
# Create precision certificate for spectral computation
spectral_data = {
    'local_data': {
        2: {'operator': [[1.0, 0.0], [0.0, 2.0]]},
        3: {'operator': [[2.0, 1.0], [1.0, 2.0]]}
    }
}

cert = verifier.create_certificate('curve_11a1', spectral_data)
print(f"Certificate status: {cert.status}")
print(f"Tests performed: {len(cert.precision_tests)}")

# Save certificate
from pathlib import Path
output_dir = Path('certificates')
output_dir.mkdir(exist_ok=True)
cert.save(output_dir / 'cert_11a1.json')
```

### Complete Certification Workflow

```python
# One-line certification with automatic saving
cert = certify_computation(
    computation_id='11a1',
    spectral_data=spectral_data,
    tolerance=1e-10,
    output_dir=Path('certificates')
)
```

### Precision Guarantees

The framework provides the following guarantees:

1. **Matrix Operations**: ≤10⁻¹⁰ relative error
   - Verified via cofactor expansion for small matrices
   - Cross-validated with multiple methods

2. **Eigenvalue Computations**: ≤10⁻¹⁰ absolute error
   - Validated via trace/determinant identities
   - Checked for numerical stability

3. **Convergence**: Documented for iterative methods
   - Cauchy sequence tests
   - Error bound tracking

4. **Mixed Precision**: Not currently used
   - All computations in IEEE 754 double precision
   - Future: explicit precision tracking for optimizations

### Certificate Format

Certificates are saved as JSON with the following structure:

```json
{
  "computation_id": "11a1",
  "timestamp": "2025-10-30T01:23:45.678910",
  "status": "certified",
  "precision_tests": [
    {
      "test": "spectral_operator",
      "result": {
        "passed": true,
        "tolerance": 1e-10,
        "detailed_results": {...}
      },
      "timestamp": "2025-10-30T01:23:45.789012"
    }
  ],
  "error_bounds": {
    "spectral_bound": {"bound": 1e-10, "unit": "absolute"},
    "determinant": {"bound": 1e-10, "unit": "relative"},
    "eigenvalue": {"bound": 1e-10, "unit": "absolute"}
  }
}
```

## Complete Validation Workflow

### Demo Script

Run the complete validation workflow:

```bash
sage -python examples/validation_workflow_demo.py
```

This demonstrates all three pillars:
1. Regression testing with multiple curves
2. Performance benchmarking with timing analysis
3. Numerical precision certification

### Automated Testing

Run validation tests:

```bash
# All validation tests
pytest tests/test_regression.py tests/test_benchmark.py tests/test_precision_certification.py -v

# Just regression tests
pytest tests/test_regression.py -v

# Just benchmarking tests
pytest tests/test_benchmark.py -v

# Just precision tests
pytest tests/test_precision_certification.py -v
```

**Test Coverage**: 40 tests covering all aspects of validation

## Best Practices

### For Researchers

1. **Always run regression tests** on new curves before publication
2. **Document benchmark results** for reproducibility
3. **Include precision certificates** with numerical results
4. **Compare with LMFDB data** when available

### For Developers

1. **Add reference data** for new test curves
2. **Benchmark new algorithms** before merging
3. **Set appropriate tolerances** based on algorithm properties
4. **Generate certificates** for critical computations

### For Users

1. **Check regression test results** before trusting outputs
2. **Review benchmark reports** to understand performance
3. **Verify precision certificates** for critical applications
4. **Report inconsistencies** via GitHub issues

## Integration with CI/CD

The validation framework integrates with GitHub Actions:

```yaml
- name: Run validation tests
  run: |
    pytest tests/test_regression.py tests/test_benchmark.py tests/test_precision_certification.py -v
```

All basic tests run without SageMath for fast CI feedback.

## References

### Regression Testing
- LMFDB: https://www.lmfdb.org/
- Cremona Database: https://johncremona.github.io/ecdata/
- Stein-Watkins: http://www.maths.bris.ac.uk/~maarb/papers/papers.html

### Benchmarking
- Complexity theory: Knuth, *The Art of Computer Programming*
- Algorithmic benchmarking: Hopcroft & Ullman, *Introduction to Automata Theory*

### Numerical Precision
- IEEE 754: Standard for Floating-Point Arithmetic
- Higham, *Accuracy and Stability of Numerical Algorithms* (2002)
- Goldberg, "What Every Computer Scientist Should Know About Floating-Point Arithmetic" (1991)

## Support

For questions or issues with validation:
- GitHub Issues: https://github.com/motanova84/adelic-bsd/issues
- Documentation: See `docs/MANUAL.md` for technical details
- Examples: See `examples/validation_workflow_demo.py`
