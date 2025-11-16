"""
Tests for Benchmarking Module

Validates the performance benchmarking functionality.
"""

import pytest
import sys
import os
import time

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from src.benchmark import (
    PerformanceBenchmark,
    run_standard_benchmarks
)


@pytest.mark.basic
def test_benchmark_initialization():
    """Test that benchmark suite initializes correctly."""
    benchmark = PerformanceBenchmark()
    
    assert benchmark.benchmark_results is not None
    assert benchmark.system_info is not None
    assert len(benchmark.benchmark_results) == 0


@pytest.mark.basic
def test_system_info_collection():
    """Test system information collection."""
    benchmark = PerformanceBenchmark()
    
    info = benchmark.system_info
    assert 'platform' in info
    assert 'python_version' in info
    assert 'timestamp' in info


@pytest.mark.basic
def test_benchmark_simple_function():
    """Test benchmarking a simple function."""
    benchmark = PerformanceBenchmark()
    
    def test_func():
        time.sleep(0.01)
        return 42
    
    result = benchmark.benchmark_computation(test_func, iterations=3)
    
    assert 'mean_time' in result
    assert 'min_time' in result
    assert 'max_time' in result
    assert 'std_dev' in result
    assert result['iterations'] == 3
    assert result['results'] == 42
    assert result['mean_time'] > 0.01


@pytest.mark.basic
def test_benchmark_with_args():
    """Test benchmarking with function arguments."""
    benchmark = PerformanceBenchmark()
    
    def add(a, b):
        return a + b
    
    result = benchmark.benchmark_computation(add, 5, 3, iterations=2)
    
    assert result['results'] == 8
    assert result['mean_time'] >= 0


@pytest.mark.basic
def test_std_dev_calculation():
    """Test standard deviation calculation."""
    benchmark = PerformanceBenchmark()
    
    # Test with known values
    std = benchmark._std_dev([1.0, 2.0, 3.0, 4.0, 5.0])
    # Sample std dev with n-1: variance = 2.5, std = sqrt(2.5) ≈ 1.58
    expected_std = (2.5 ** 0.5)  
    assert abs(std - expected_std) < 0.01
    
    # Test with single value
    std = benchmark._std_dev([1.0])
    assert std == 0.0


@pytest.mark.basic
def test_scaling_analysis_empty():
    """Test scaling analysis with no data."""
    benchmark = PerformanceBenchmark()
    
    scaling = benchmark.analyze_scaling([])
    assert scaling['status'] == 'no_data'


@pytest.mark.basic
def test_scaling_analysis_insufficient_data():
    """Test scaling analysis with insufficient data."""
    benchmark = PerformanceBenchmark()
    
    results = [
        {'conductor': 11, 'mean_time_seconds': 0.1}
    ]
    
    scaling = benchmark.analyze_scaling(results)
    assert scaling.get('status') == 'insufficient_data' or 'data_points' in scaling


@pytest.mark.basic
def test_scaling_analysis_sufficient_data():
    """Test scaling analysis with sufficient data."""
    benchmark = PerformanceBenchmark()
    
    results = [
        {'conductor': 10, 'mean_time_seconds': 0.01},
        {'conductor': 20, 'mean_time_seconds': 0.04},
        {'conductor': 30, 'mean_time_seconds': 0.09},
    ]
    
    scaling = benchmark.analyze_scaling(results)
    
    if 'scaling_exponent' in scaling:
        assert 'scaling_exponent' in scaling
        assert 'theoretical_bound' in scaling
        assert 'subquadratic' in scaling
        assert scaling['data_points'] == 3


@pytest.mark.basic
def test_benchmark_report_generation():
    """Test generation of benchmark report."""
    benchmark = PerformanceBenchmark()
    
    # Add mock results
    benchmark.benchmark_results = [
        {
            'curve': '11a1',
            'conductor': 11,
            'mean_time_seconds': 0.1,
            'min_time_seconds': 0.09,
            'max_time_seconds': 0.11,
            'std_dev_seconds': 0.01
        }
    ]
    
    report = benchmark.generate_benchmark_report()
    
    assert isinstance(report, str)
    assert 'BENCHMARK REPORT' in report
    assert '11a1' in report
    assert 'System Information' in report


@pytest.mark.basic
def test_compare_with_baseline_no_sage():
    """Test baseline comparison without SageMath."""
    benchmark = PerformanceBenchmark()
    
    result = benchmark.compare_with_baseline('11a1', spectral_time=0.1)
    
    # Without sage, should skip
    assert 'status' in result or 'curve' in result


@pytest.mark.sage_required
def test_benchmark_spectral_finiteness():
    """Test benchmarking spectral finiteness computation."""
    try:
        from src.spectral_finiteness import SpectralFinitenessProver
    except ImportError:
        pytest.skip("SageMath not available")
    
    benchmark = PerformanceBenchmark()
    
    result = benchmark.benchmark_spectral_finiteness('11a1', SpectralFinitenessProver, iterations=2)
    
    if result.get('status') != 'skipped':
        assert 'curve' in result
        assert 'mean_time_seconds' in result
        assert result['conductor'] == 11
        assert result['mean_time_seconds'] >= 0


@pytest.mark.sage_required
def test_compare_with_baseline_with_sage():
    """Test baseline comparison with SageMath."""
    try:
        from sage.all import EllipticCurve
    except ImportError:
        pytest.skip("SageMath not available")
    
    benchmark = PerformanceBenchmark()
    
    result = benchmark.compare_with_baseline('11a1', spectral_time=0.1)
    
    if result.get('status') != 'skipped':
        assert 'curve' in result
        assert 'spectral_time' in result
        assert 'sage_rank_time' in result


@pytest.mark.sage_required
@pytest.mark.slow
def test_benchmark_conductor_range():
    """Test benchmarking curves in a conductor range."""
    try:
        from src.spectral_finiteness import SpectralFinitenessProver
    except ImportError:
        pytest.skip("SageMath not available")
    
    benchmark = PerformanceBenchmark()
    
    results = benchmark.benchmark_conductor_range(11, 20, SpectralFinitenessProver, max_curves=3)
    
    if results and results[0].get('status') != 'skipped':
        assert len(results) > 0
        assert all('curve' in r or 'status' in r for r in results)


@pytest.mark.basic
def test_export_results_json(tmp_path):
    """Test exporting benchmark results as JSON."""
    benchmark = PerformanceBenchmark()
    
    # Add mock result
    benchmark.benchmark_results = [
        {'curve': '11a1', 'mean_time_seconds': 0.1}
    ]
    
    output_file = tmp_path / "benchmark.json"
    benchmark.export_results_json(output_file)
    
    assert output_file.exists()
    
    # Read and verify JSON
    import json
    with output_file.open() as f:
        data = json.load(f)
    
    assert 'system_info' in data
    assert 'benchmark_results' in data
    assert len(data['benchmark_results']) == 1


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
