#!/usr/bin/env python3
"""
BSD Estimator of |Ш| for curves with rank ≥ 2

Implements the BSD formula to estimate the order of the Tate-Shafarevich group:

    |Ш(E)| = L^{(r)}(E,1) / (r! · Ω_E · R_E · |Tors(E)|² · ∏c_p)

Where:
    - L^{(r)}(E,1) = r-th derivative of the L-series at s=1
    - r = analytic rank of E
    - Ω_E = real (or complex) period
    - R_E = regulator
    - Tors(E) = torsion subgroup order
    - ∏c_p = product of Tamagawa numbers

Part of the BSD-10000 → GO · Paso 9 operation.

Author: adelic-bsd contributors
Date: November 2025
License: MIT
"""

import os
import sys
import csv
import json
import argparse
from datetime import datetime
from pathlib import Path
from math import factorial

# Try to import SageMath
try:
    from sage.all import EllipticCurve, prod, RR, cremona_curves
    SAGE_AVAILABLE = True
except ImportError:
    SAGE_AVAILABLE = False


# Constants
DENOMINATOR_THRESHOLD = 1e-100
CSV_FIELD_NAMES = [
    'label', 'rank', 'sha_estimate', 'l_derivative',
    'omega', 'R', 'torsion', 'tamagawa'
]
DEFAULT_CONDUCTOR_MAX_RANK2 = 100000
DEFAULT_CONDUCTOR_MAX_RANK3 = 500000

# Precomputed factorials for common ranks to improve performance
FACTORIAL_CACHE = {i: factorial(i) for i in range(10)}


def cached_factorial(n):
    """Return factorial with caching for common values."""
    if n in FACTORIAL_CACHE:
        return FACTORIAL_CACHE[n]
    return factorial(n)


class ShaEstimator:
    """
    Estimator for |Ш(E)| using the BSD formula for curves with rank ≥ 2.
    
    Implements SABIO ∞³ estimation protocol for Tate-Shafarevich groups.
    """
    
    def __init__(self, digits=10, verbose=False):
        """
        Initialize the estimator.
        
        Args:
            digits: Precision digits for numerical computation
            verbose: Print detailed progress messages
        """
        self.digits = digits
        self.verbose = verbose
        self.results = []
        
    def log(self, message):
        """Print message if verbose mode is enabled."""
        if self.verbose:
            print(message)
    
    def estimate_sha(self, label):
        """
        Estimate |Ш(E)| for a single curve.
        
        Args:
            label: LMFDB label or Cremona label (e.g., '389a1')
        
        Returns:
            dict with estimation results or None if rank < 2
        """
        if not SAGE_AVAILABLE:
            return {
                'label': label,
                'error': 'SageMath not available',
                'success': False
            }
        
        try:
            # Load curve (try LMFDB label first, then Cremona)
            try:
                E = EllipticCurve(lmfdb_label=label)
            except (ValueError, TypeError):
                E = EllipticCurve(label)
            
            # Get rank
            r = E.rank()
            
            # Only process curves with rank ≥ 2
            if r < 2:
                return None
            
            self.log(f"Processing {label} (rank {r})...")
            
            # Compute BSD components
            # L^{(r)}(1) - r-th derivative of L-function at s=1
            L_series = E.lseries()
            Lr = L_series.derivative(r)(1)
            
            # Torsion order
            tors_order = E.torsion_order()
            
            # Regulator (height pairing determinant)
            R = E.regulator()
            
            # Real period (via period lattice)
            Omega = E.period_lattice().real_volume()
            
            # Product of Tamagawa numbers
            tamagawa = prod(E.tamagawa_numbers())
            
            # BSD formula: |Ш| = L^{(r)}(1) / (r! · Ω · R · |Tors|² · ∏c_p)
            denominator = cached_factorial(r) * Omega * R * (tors_order ** 2) * tamagawa
            
            if abs(denominator) < DENOMINATOR_THRESHOLD:
                return {
                    'label': label,
                    'rank': r,
                    'error': 'Denominator too small',
                    'success': False
                }
            
            sha_estimate = Lr / denominator
            
            # Numerical approximation
            sha_numerical = float(RR(sha_estimate).n(digits=self.digits))
            
            result = {
                'label': label,
                'rank': int(r),
                'sha_estimate': sha_numerical,
                'l_derivative': float(RR(Lr).n(digits=self.digits)),
                'omega': float(RR(Omega).n(digits=self.digits)),
                'R': float(RR(R).n(digits=self.digits)),
                'torsion': int(tors_order),
                'tamagawa': int(tamagawa),
                'conductor': int(E.conductor()),
                'success': True,
                'timestamp': datetime.now().isoformat()
            }
            
            self.log(f"  ✓ |Ш| ≈ {sha_numerical:.6f}")
            self.results.append(result)
            
            return result
            
        except Exception as e:
            error_result = {
                'label': label,
                'error': str(e),
                'success': False
            }
            self.log(f"  ✗ Error: {e}")
            return error_result
    
    def batch_estimate(self, labels, output_csv=None, output_json=None):
        """
        Estimate |Ш| for multiple curves.
        
        Args:
            labels: List of curve labels
            output_csv: Path to save CSV results
            output_json: Path to save JSON results
        
        Returns:
            dict with batch results and statistics
        """
        self.log(f"\n{'='*70}")
        self.log("BATCH SHA ESTIMATION")
        self.log(f"{'='*70}")
        self.log(f"Total curves to process: {len(labels)}")
        self.log(f"Precision: {self.digits} digits")
        self.log(f"{'='*70}\n")
        
        results = []
        success_count = 0
        skip_count = 0
        error_count = 0
        
        for i, label in enumerate(labels):
            if self.verbose:
                print(f"[{i+1}/{len(labels)}] ", end="")
            
            result = self.estimate_sha(label)
            
            if result is None:
                skip_count += 1
            elif result.get('success', False):
                success_count += 1
                results.append(result)
            else:
                error_count += 1
                results.append(result)
        
        # Generate summary
        summary = {
            'total_curves': len(labels),
            'processed': len(results),
            'success': success_count,
            'errors': error_count,
            'skipped_low_rank': skip_count,
            'timestamp': datetime.now().isoformat(),
            'precision_digits': self.digits
        }
        
        # Statistics by rank
        rank_stats = {}
        for r in results:
            if r.get('success') and 'rank' in r:
                rank = r['rank']
                if rank not in rank_stats:
                    rank_stats[rank] = {'count': 0, 'sha_values': []}
                rank_stats[rank]['count'] += 1
                rank_stats[rank]['sha_values'].append(r['sha_estimate'])
        
        summary['by_rank'] = rank_stats
        
        # Save results
        successful_results = [r for r in results if r.get('success', False)]
        
        if output_csv and successful_results:
            self._save_csv(successful_results, output_csv)
        
        if output_json:
            self._save_json({'summary': summary, 'results': results}, output_json)
        
        # Print summary
        if self.verbose:
            self._print_summary(summary)
        
        return {
            'summary': summary,
            'results': results
        }
    
    def _save_csv(self, results, filepath):
        """Save results to CSV file."""
        filepath = Path(filepath)
        filepath.parent.mkdir(parents=True, exist_ok=True)
        
        with open(filepath, 'w', newline='') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=CSV_FIELD_NAMES, 
                                   extrasaction='ignore')
            writer.writeheader()
            writer.writerows(results)
        
        self.log(f"\n📄 CSV saved: {filepath}")
    
    def _save_json(self, data, filepath):
        """Save results to JSON file."""
        filepath = Path(filepath)
        filepath.parent.mkdir(parents=True, exist_ok=True)
        
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2, default=str)
        
        self.log(f"📄 JSON saved: {filepath}")
    
    def _print_summary(self, summary):
        """Print summary statistics."""
        print(f"\n{'='*70}")
        print("ESTIMATION SUMMARY")
        print(f"{'='*70}")
        print(f"Total curves: {summary['total_curves']}")
        print(f"Processed: {summary['processed']}")
        print(f"Successful: {summary['success']}")
        print(f"Errors: {summary['errors']}")
        print(f"Skipped (rank < 2): {summary['skipped_low_rank']}")
        
        if summary['by_rank']:
            print(f"\nBy rank:")
            for rank, stats in sorted(summary['by_rank'].items()):
                print(f"  Rank {rank}: {stats['count']} curves")
        
        print(f"{'='*70}")


def estimate_sha(label, digits=10):
    """
    Convenience function to estimate |Ш| for a single curve.
    
    Args:
        label: LMFDB or Cremona label
        digits: Precision digits
    
    Returns:
        Numerical estimate of |Ш| or None if rank < 2
    """
    estimator = ShaEstimator(digits=digits, verbose=False)
    result = estimator.estimate_sha(label)
    
    if result is None or not result.get('success', False):
        return None
    
    return result['sha_estimate']


def batch_sha_estimation(labels, output_csv=None, output_json=None, 
                         digits=10, verbose=True):
    """
    Batch estimation of |Ш| for multiple curves.
    
    Args:
        labels: List of curve labels
        output_csv: Path to CSV output file
        output_json: Path to JSON output file
        digits: Precision digits
        verbose: Print progress
    
    Returns:
        dict with summary and results
    """
    estimator = ShaEstimator(digits=digits, verbose=verbose)
    return estimator.batch_estimate(labels, output_csv, output_json)


def get_curves_by_rank(min_rank=2, max_rank=None, conductor_max=1000, limit=None):
    """
    Get curves from Cremona database by rank.
    
    Args:
        min_rank: Minimum rank (default 2)
        max_rank: Maximum rank (default None = no limit)
        conductor_max: Maximum conductor to search
        limit: Maximum number of curves to return
    
    Returns:
        List of curve labels
    """
    if not SAGE_AVAILABLE:
        # Return known curves with rank ≥ 2 as fallback
        fallback = [
            # Rank 2 curves
            '389a1', '433a1', '446d1', '563a1', '571a1', 
            '643a1', '655a1', '681c1', '707a1', '709a1',
            '718b1', '794a1', '817a1', '916c1', '997b1',
            # Rank 3 curves (if available)
            '5077a1', '234446a1',
        ]
        if limit:
            return fallback[:limit]
        return fallback
    
    curves = []
    
    for N in range(1, conductor_max + 1):
        try:
            for E in cremona_curves(N):
                r = E.rank()
                if r >= min_rank and (max_rank is None or r <= max_rank):
                    curves.append(E.cremona_label())
                    if limit and len(curves) >= limit:
                        return curves
        except (StopIteration, RuntimeError):
            continue
    
    return curves


def run_bsd_10000_paso9(rank2_limit=500, rank3_limit=50, 
                        output_dir=None, verbose=True):
    """
    Execute the BSD-10000 → GO · Paso 9 operation.
    
    Processes:
        - Up to 500 curves with rank 2
        - Up to 50 curves with rank 3 (if available)
    
    Args:
        rank2_limit: Maximum rank 2 curves to process
        rank3_limit: Maximum rank 3 curves to process
        output_dir: Output directory for results
        verbose: Print progress
    
    Returns:
        dict with all results
    """
    if output_dir is None:
        output_dir = Path(__file__).parent / 'results'
    else:
        output_dir = Path(output_dir)
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    
    # Collect curves
    if verbose:
        print("Collecting curves with rank ≥ 2...")
    
    rank2_curves = get_curves_by_rank(min_rank=2, max_rank=2, 
                                       conductor_max=DEFAULT_CONDUCTOR_MAX_RANK2, 
                                       limit=rank2_limit)
    rank3_curves = get_curves_by_rank(min_rank=3, max_rank=3, 
                                       conductor_max=DEFAULT_CONDUCTOR_MAX_RANK3, 
                                       limit=rank3_limit)
    
    all_curves = rank2_curves + rank3_curves
    
    if verbose:
        print(f"Found {len(rank2_curves)} rank 2 curves")
        print(f"Found {len(rank3_curves)} rank 3 curves")
    
    # Run batch estimation
    results = batch_sha_estimation(
        all_curves,
        output_csv=output_dir / f'sha_estimation_{timestamp}.csv',
        output_json=output_dir / f'sha_estimation_{timestamp}.json',
        digits=10,
        verbose=verbose
    )
    
    return results


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='BSD Estimator of |Ш| for curves with rank ≥ 2',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Estimate Sha for a single curve
  python estimate_sha.py --curve 389a1
  
  # Batch process multiple curves
  python estimate_sha.py --curve 389a1 --curve 433a1 --curve 5077a1
  
  # Run full BSD-10000 Paso 9 operation
  python estimate_sha.py --run-paso9
  
  # Process curves from conductor range
  python estimate_sha.py --conductor-max 1000 --rank-min 2 --limit 100
        """
    )
    
    parser.add_argument('--curve', '-c', action='append', dest='curves',
                        help='Curve label (can specify multiple)')
    parser.add_argument('--run-paso9', action='store_true',
                        help='Run full BSD-10000 Paso 9 operation')
    parser.add_argument('--conductor-max', type=int, default=1000,
                        help='Maximum conductor for curve search')
    parser.add_argument('--rank-min', type=int, default=2,
                        help='Minimum rank to process')
    parser.add_argument('--limit', type=int,
                        help='Maximum curves to process')
    parser.add_argument('--output', '-o', default='results',
                        help='Output directory')
    parser.add_argument('--digits', '-d', type=int, default=10,
                        help='Precision digits')
    parser.add_argument('--quiet', '-q', action='store_true',
                        help='Suppress progress messages')
    
    args = parser.parse_args()
    verbose = not args.quiet
    output_dir = Path(args.output)
    
    if args.run_paso9:
        # Run full BSD-10000 Paso 9 operation
        results = run_bsd_10000_paso9(output_dir=output_dir, verbose=verbose)
        
    elif args.curves:
        # Process specified curves
        results = batch_sha_estimation(
            args.curves,
            output_csv=output_dir / 'sha_estimation.csv',
            output_json=output_dir / 'sha_estimation.json',
            digits=args.digits,
            verbose=verbose
        )
        
    else:
        # Search for curves by conductor
        if verbose:
            print(f"Searching for curves with rank ≥ {args.rank_min}...")
        
        curves = get_curves_by_rank(
            min_rank=args.rank_min,
            conductor_max=args.conductor_max,
            limit=args.limit
        )
        
        if not curves:
            print("No curves found matching criteria")
            return 1
        
        results = batch_sha_estimation(
            curves,
            output_csv=output_dir / 'sha_estimation.csv',
            output_json=output_dir / 'sha_estimation.json',
            digits=args.digits,
            verbose=verbose
        )
    
    # Print final message
    if verbose and results:
        success_rate = results['summary']['success'] / max(results['summary']['processed'], 1)
        print(f"\n✅ Estimation complete. Success rate: {success_rate:.1%}")
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
