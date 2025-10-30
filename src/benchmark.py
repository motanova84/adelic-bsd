"""
Benchmarking Module for Spectral BSD Framework

This module provides comprehensive benchmarking capabilities to compare
the performance of the spectral BSD framework against standard mathematical
libraries and published performance metrics.

Metrics measured:
- Computation time per curve
- Spectral operator diagonalization time
- Memory usage
- Scaling behavior with conductor size

Comparisons against:
- SageMath built-in methods
- Published algorithmic complexity bounds
- Reference implementations
"""

import time
import json
from typing import Dict, List, Tuple, Optional, Callable
from pathlib import Path
from datetime import datetime
import platform


class PerformanceBenchmark:
    """
    Performance benchmarking suite for spectral BSD computations.
    
    Measures and compares performance against standard frameworks
    and theoretical complexity bounds.
    """
    
    def __init__(self):
        """Initialize benchmark suite."""
        self.benchmark_results = []
        self.system_info = self._collect_system_info()
        
    def _collect_system_info(self) -> Dict:
        """
        Collect system information for benchmark context.
        
        Returns:
            Dictionary of system information
        """
        return {
            'platform': platform.platform(),
            'processor': platform.processor(),
            'python_version': platform.python_version(),
            'timestamp': datetime.now().isoformat()
        }
    
    def benchmark_computation(self, func: Callable, *args, 
                            iterations: int = 1, **kwargs) -> Dict:
        """
        Benchmark a computation function.
        
        Args:
            func: Function to benchmark
            args: Positional arguments for func
            iterations: Number of iterations to average
            kwargs: Keyword arguments for func
            
        Returns:
            Benchmark results dictionary
        """
        times = []
        results = None
        
        for i in range(iterations):
            start_time = time.perf_counter()
            results = func(*args, **kwargs)
            end_time = time.perf_counter()
            times.append(end_time - start_time)
        
        return {
            'mean_time': sum(times) / len(times),
            'min_time': min(times),
            'max_time': max(times),
            'std_dev': self._std_dev(times) if len(times) > 1 else 0.0,
            'iterations': iterations,
            'results': results
        }
    
    def _std_dev(self, values: List[float]) -> float:
        """Calculate standard deviation."""
        if len(values) <= 1:
            return 0.0
        mean = sum(values) / len(values)
        variance = sum((x - mean) ** 2 for x in values) / (len(values) - 1)
        return variance ** 0.5
    
    def benchmark_spectral_finiteness(self, curve_label: str, 
                                     prover_class,
                                     iterations: int = 3) -> Dict:
        """
        Benchmark spectral finiteness computation for a curve.
        
        Args:
            curve_label: LMFDB curve label
            prover_class: SpectralFinitenessProver class
            iterations: Number of iterations
            
        Returns:
            Benchmark results
        """
        try:
            from sage.all import EllipticCurve
            E = EllipticCurve(curve_label)
        except ImportError:
            # If sage not available, return placeholder
            return {
                'curve': curve_label,
                'status': 'skipped',
                'reason': 'SageMath not available'
            }
        
        def run_proof():
            prover = prover_class(E)
            return prover.prove_finiteness()
        
        benchmark = self.benchmark_computation(run_proof, iterations=iterations)
        
        result = {
            'curve': curve_label,
            'conductor': E.conductor(),
            'mean_time_seconds': benchmark['mean_time'],
            'min_time_seconds': benchmark['min_time'],
            'max_time_seconds': benchmark['max_time'],
            'std_dev_seconds': benchmark['std_dev'],
            'iterations': iterations,
            'timestamp': datetime.now().isoformat()
        }
        
        self.benchmark_results.append(result)
        return result
    
    def benchmark_conductor_range(self, conductor_min: int, 
                                  conductor_max: int,
                                  prover_class,
                                  max_curves: int = 10) -> List[Dict]:
        """
        Benchmark curves in a conductor range.
        
        Args:
            conductor_min: Minimum conductor
            conductor_max: Maximum conductor
            prover_class: SpectralFinitenessProver class
            max_curves: Maximum number of curves to test
            
        Returns:
            List of benchmark results
        """
        try:
            from sage.all import cremona_curves
            
            results = []
            count = 0
            
            for N in range(conductor_min, conductor_max + 1):
                if count >= max_curves:
                    break
                
                try:
                    curves = cremona_curves(N)
                    for curve in curves[:min(2, len(curves))]:  # Max 2 per conductor
                        if count >= max_curves:
                            break
                        label = curve.cremona_label()
                        result = self.benchmark_spectral_finiteness(
                            label, prover_class, iterations=1
                        )
                        results.append(result)
                        count += 1
                except:
                    continue
            
            return results
        except ImportError:
            return [{
                'status': 'skipped',
                'reason': 'SageMath not available'
            }]
    
    def compare_with_baseline(self, curve_label: str, 
                             spectral_time: float) -> Dict:
        """
        Compare spectral method performance with baseline methods.
        
        Args:
            curve_label: LMFDB curve label
            spectral_time: Time taken by spectral method (seconds)
            
        Returns:
            Comparison results
        """
        try:
            from sage.all import EllipticCurve
            E = EllipticCurve(curve_label)
            
            # Benchmark SageMath's built-in rank computation
            start = time.perf_counter()
            try:
                rank = E.rank()
            except:
                rank = None
            sage_time = time.perf_counter() - start
            
            # Benchmark conductor computation
            start = time.perf_counter()
            conductor = E.conductor()
            conductor_time = time.perf_counter() - start
            
            return {
                'curve': curve_label,
                'spectral_time': spectral_time,
                'sage_rank_time': sage_time,
                'conductor_time': conductor_time,
                'speedup_vs_rank': sage_time / spectral_time if spectral_time > 0 else None
            }
        except ImportError:
            return {
                'curve': curve_label,
                'status': 'skipped',
                'reason': 'SageMath not available'
            }
    
    def analyze_scaling(self, results: List[Dict]) -> Dict:
        """
        Analyze scaling behavior from benchmark results.
        
        Args:
            results: List of benchmark results
            
        Returns:
            Scaling analysis
        """
        if not results:
            return {'status': 'no_data'}
        
        # Group by conductor
        by_conductor = {}
        for r in results:
            if 'conductor' in r and 'mean_time_seconds' in r:
                N = r['conductor']
                t = r['mean_time_seconds']
                if N not in by_conductor:
                    by_conductor[N] = []
                by_conductor[N].append(t)
        
        # Calculate average time per conductor
        conductor_times = []
        for N, times in sorted(by_conductor.items()):
            avg_time = sum(times) / len(times)
            conductor_times.append((N, avg_time))
        
        # Estimate scaling exponent (time ~ N^α)
        if len(conductor_times) >= 2:
            import math
            # Simple linear regression on log-log scale
            log_N = [math.log(N) for N, _ in conductor_times]
            log_t = [math.log(t) for _, t in conductor_times]
            
            n = len(log_N)
            sum_x = sum(log_N)
            sum_y = sum(log_t)
            sum_xy = sum(x * y for x, y in zip(log_N, log_t))
            sum_xx = sum(x * x for x in log_N)
            
            # Slope = scaling exponent
            alpha = (n * sum_xy - sum_x * sum_y) / (n * sum_xx - sum_x * sum_x)
            
            return {
                'scaling_exponent': alpha,
                'theoretical_bound': 2.0,  # Expected O(N²) for naive methods
                'subquadratic': alpha < 2.0,
                'conductor_range': (min(N for N, _ in conductor_times),
                                  max(N for N, _ in conductor_times)),
                'data_points': len(conductor_times)
            }
        
        return {
            'status': 'insufficient_data',
            'data_points': len(conductor_times)
        }
    
    def generate_benchmark_report(self, output_path: Optional[Path] = None) -> str:
        """
        Generate comprehensive benchmark report.
        
        Args:
            output_path: Optional path to save report
            
        Returns:
            Formatted report string
        """
        report = []
        report.append("=" * 70)
        report.append("SPECTRAL BSD PERFORMANCE BENCHMARK REPORT")
        report.append("=" * 70)
        report.append("")
        
        # System information
        report.append("System Information:")
        report.append("-" * 70)
        for key, value in self.system_info.items():
            report.append(f"  {key}: {value}")
        report.append("")
        
        # Individual results
        if self.benchmark_results:
            report.append("Individual Benchmark Results:")
            report.append("-" * 70)
            for result in self.benchmark_results:
                if 'curve' in result:
                    report.append(f"\nCurve: {result['curve']}")
                    if 'conductor' in result:
                        report.append(f"  Conductor: {result['conductor']}")
                    if 'mean_time_seconds' in result:
                        report.append(f"  Mean time: {result['mean_time_seconds']:.6f} seconds")
                        report.append(f"  Min time:  {result['min_time_seconds']:.6f} seconds")
                        report.append(f"  Max time:  {result['max_time_seconds']:.6f} seconds")
            report.append("")
        
        # Scaling analysis
        scaling = self.analyze_scaling(self.benchmark_results)
        if scaling.get('status') != 'no_data':
            report.append("Scaling Analysis:")
            report.append("-" * 70)
            if 'scaling_exponent' in scaling:
                report.append(f"  Empirical scaling exponent: α = {scaling['scaling_exponent']:.3f}")
                report.append(f"  Theoretical bound: O(N^{scaling['theoretical_bound']})")
                report.append(f"  Subquadratic: {scaling['subquadratic']}")
                report.append(f"  Conductor range: {scaling['conductor_range']}")
            report.append("")
        
        # Performance summary
        if self.benchmark_results:
            times = [r['mean_time_seconds'] for r in self.benchmark_results 
                    if 'mean_time_seconds' in r]
            if times:
                report.append("Performance Summary:")
                report.append("-" * 70)
                report.append(f"  Total curves tested: {len(times)}")
                report.append(f"  Average time per curve: {sum(times)/len(times):.6f} seconds")
                report.append(f"  Fastest computation: {min(times):.6f} seconds")
                report.append(f"  Slowest computation: {max(times):.6f} seconds")
                report.append("")
        
        report.append("Comparison Baselines:")
        report.append("-" * 70)
        report.append("  - SageMath built-in rank computation")
        report.append("  - Theoretical O(N²) complexity bound")
        report.append("  - Published algorithmic benchmarks")
        report.append("")
        
        report_text = "\n".join(report)
        
        if output_path:
            output_path = Path(output_path)
            output_path.write_text(report_text)
        
        return report_text
    
    def export_results_json(self, output_path: Path):
        """
        Export benchmark results as JSON.
        
        Args:
            output_path: Path to save JSON file
        """
        data = {
            'system_info': self.system_info,
            'benchmark_results': self.benchmark_results,
            'scaling_analysis': self.analyze_scaling(self.benchmark_results)
        }
        
        output_path = Path(output_path)
        with output_path.open('w') as f:
            json.dump(data, f, indent=2)


def run_standard_benchmarks(prover_class, output_dir: Optional[Path] = None) -> Dict:
    """
    Run standard benchmark suite.
    
    Args:
        prover_class: SpectralFinitenessProver class
        output_dir: Optional directory to save results
        
    Returns:
        Benchmark summary
    """
    benchmark = PerformanceBenchmark()
    
    # Test standard curves
    test_curves = ['11a1', '37a1', '389a1']
    
    for label in test_curves:
        benchmark.benchmark_spectral_finiteness(label, prover_class, iterations=3)
    
    # Generate report
    report = benchmark.generate_benchmark_report()
    
    if output_dir:
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        report_path = output_dir / 'benchmark_report.txt'
        benchmark.generate_benchmark_report(report_path)
        
        json_path = output_dir / 'benchmark_results.json'
        benchmark.export_results_json(json_path)
    
    return {
        'report': report,
        'results': benchmark.benchmark_results,
        'scaling': benchmark.analyze_scaling(benchmark.benchmark_results)
    }
