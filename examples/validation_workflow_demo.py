#!/usr/bin/env python3
"""
Comprehensive Validation Workflow Demo

This script demonstrates the complete validation, benchmarking, and precision
certification workflow for the Spectral BSD framework.

Usage:
    sage -python examples/validation_workflow_demo.py
"""

import sys
import os
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.regression_tests import RegressionTestSuite, validate_against_literature
from src.benchmark import PerformanceBenchmark
from src.precision_certification import PrecisionVerifier, certify_computation


def demo_regression_testing():
    """Demonstrate regression testing against known results."""
    print("=" * 70)
    print("REGRESSION TESTING DEMO")
    print("=" * 70)
    print()
    
    suite = RegressionTestSuite()
    
    # Simulate some computation results
    test_curves = {
        '11a1': {'spectral_bound': 1, 'conductor': 11, 'rank': 0},
        '37a1': {'spectral_bound': 1, 'conductor': 37, 'rank': 1},
        '389a1': {'spectral_bound': 1, 'conductor': 389, 'rank': 2}
    }
    
    print("Testing computed results against literature...")
    for label, results in test_curves.items():
        print(f"\nCurve {label}:")
        
        # Test spectral bound
        result = suite.test_spectral_bound_consistency(label, results['spectral_bound'])
        print(f"  Spectral bound: {result['status']}")
        
        # Test conductor
        result = suite.test_conductor_computation(label, results['conductor'])
        print(f"  Conductor: {result['status']}")
        
        # Test rank
        result = suite.test_rank_prediction(label, results['rank'])
        print(f"  Rank: {result['status']}")
    
    # Generate report
    print("\n" + "-" * 70)
    summary = suite.run_full_regression_suite()
    print(f"\nRegression Test Summary:")
    print(f"  Total: {summary['total_tests']}")
    print(f"  Passed: {summary['passed']}")
    print(f"  Failed: {summary['failed']}")
    print()


def demo_benchmarking():
    """Demonstrate performance benchmarking."""
    print("=" * 70)
    print("BENCHMARKING DEMO")
    print("=" * 70)
    print()
    
    benchmark = PerformanceBenchmark()
    
    # Simulate some benchmark results
    print("System Information:")
    for key, value in benchmark.system_info.items():
        print(f"  {key}: {value}")
    print()
    
    # Simple function benchmark
    import time
    def sample_computation():
        time.sleep(0.001)  # Simulate computation
        return 42
    
    print("Benchmarking sample computation...")
    result = benchmark.benchmark_computation(sample_computation, iterations=5)
    print(f"  Mean time: {result['mean_time']:.6f} seconds")
    print(f"  Min time:  {result['min_time']:.6f} seconds")
    print(f"  Max time:  {result['max_time']:.6f} seconds")
    print(f"  Std dev:   {result['std_dev']:.6f} seconds")
    print()
    
    # Mock spectral finiteness results
    benchmark.benchmark_results = [
        {
            'curve': '11a1',
            'conductor': 11,
            'mean_time_seconds': 0.123,
            'min_time_seconds': 0.120,
            'max_time_seconds': 0.126,
            'std_dev_seconds': 0.003
        },
        {
            'curve': '37a1',
            'conductor': 37,
            'mean_time_seconds': 0.234,
            'min_time_seconds': 0.230,
            'max_time_seconds': 0.238,
            'std_dev_seconds': 0.004
        }
    ]
    
    scaling = benchmark.analyze_scaling(benchmark.benchmark_results)
    if 'scaling_exponent' in scaling:
        print("Scaling Analysis:")
        print(f"  Empirical exponent: α = {scaling['scaling_exponent']:.3f}")
        print(f"  Theoretical bound: O(N^{scaling['theoretical_bound']})")
        print(f"  Subquadratic: {scaling['subquadratic']}")
    print()


def demo_precision_certification():
    """Demonstrate numerical precision certification."""
    print("=" * 70)
    print("PRECISION CERTIFICATION DEMO")
    print("=" * 70)
    print()
    
    import numpy as np
    
    verifier = PrecisionVerifier(tolerance=1e-10)
    
    # Test matrix determinant precision
    print("Testing matrix determinant precision...")
    matrix = np.array([[1.0, 2.0], [3.0, 4.0]])
    result = verifier.verify_matrix_determinant(matrix, expected=-2.0)
    print(f"  Status: {'✓ PASSED' if result['passed'] else '✗ FAILED'}")
    print(f"  Computed det: {result['det_numpy']:.10f}")
    print(f"  Expected det: -2.0")
    print(f"  Error: {result.get('absolute_error', 0):.2e}")
    print()
    
    # Test eigenvalue precision
    print("Testing eigenvalue precision...")
    matrix = np.array([[2.0, 1.0], [1.0, 2.0]])
    result = verifier.verify_eigenvalues(matrix)
    print(f"  Status: {'✓ PASSED' if result['passed'] else '✗ FAILED'}")
    print(f"  Trace: {result['trace']:.10f}")
    print(f"  Sum eigenvalues: {result['sum_eigenvalues']:.10f}")
    print(f"  Trace error: {result['trace_error']:.2e}")
    print()
    
    # Create precision certificate for mock spectral data
    print("Creating precision certificate...")
    spectral_data = {
        'local_data': {
            2: {'operator': [[1.0, 0.0], [0.0, 2.0]]},
            3: {'operator': [[2.0, 1.0], [1.0, 2.0]]}
        }
    }
    
    cert = verifier.create_certificate('demo_computation', spectral_data)
    print(f"  Certificate ID: {cert.computation_id}")
    print(f"  Status: {cert.status}")
    print(f"  Tests performed: {len(cert.precision_tests)}")
    print(f"  Error bounds: {len(cert.error_bounds)}")
    print()


def demo_with_sage():
    """Demonstrate validation with actual SageMath computations."""
    print("=" * 70)
    print("VALIDATION WITH SAGEMATH")
    print("=" * 70)
    print()
    
    try:
        from sage.all import EllipticCurve
        from src.spectral_finiteness import SpectralFinitenessProver
        
        print("Running actual spectral finiteness computation...")
        E = EllipticCurve('11a1')
        prover = SpectralFinitenessProver(E)
        result = prover.prove_finiteness()
        
        print(f"\nCurve: {result['curve_label']}")
        print(f"Finiteness proved: {result['finiteness_proved']}")
        print(f"Spectral bound: {result['global_bound']}")
        print()
        
        # Validate against literature
        suite = RegressionTestSuite()
        bound_result = suite.test_spectral_bound_consistency('11a1', result['global_bound'])
        print(f"Literature validation: {bound_result['status']}")
        print(f"Known Sha: {bound_result['known_sha']}")
        print()
        
        # Benchmark the computation
        benchmark = PerformanceBenchmark()
        print("Benchmarking computation...")
        bench_result = benchmark.benchmark_spectral_finiteness('11a1', SpectralFinitenessProver, iterations=3)
        
        if bench_result.get('status') != 'skipped':
            print(f"Mean time: {bench_result['mean_time_seconds']:.6f} seconds")
        print()
        
        # Certify precision
        verifier = PrecisionVerifier()
        cert = verifier.create_certificate('11a1', result['spectral_data'])
        print(f"Precision certificate: {cert.status}")
        print()
        
    except ImportError:
        print("SageMath not available. Skipping SageMath-based demos.")
        print("Install SageMath to run full validation workflow.")
        print()


def main():
    """Run all demos."""
    print("\n")
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 15 + "SPECTRAL BSD VALIDATION WORKFLOW" + " " * 21 + "║")
    print("╚" + "═" * 68 + "╝")
    print()
    
    demo_regression_testing()
    print("\n")
    
    demo_benchmarking()
    print("\n")
    
    demo_precision_certification()
    print("\n")
    
    demo_with_sage()
    
    print("=" * 70)
    print("VALIDATION WORKFLOW COMPLETE")
    print("=" * 70)
    print()
    print("Summary:")
    print("  ✓ Regression testing against known results")
    print("  ✓ Performance benchmarking and scaling analysis")
    print("  ✓ Numerical precision certification")
    print()
    print("All validation frameworks are operational and ready for use.")
    print()


if __name__ == '__main__':
    main()
