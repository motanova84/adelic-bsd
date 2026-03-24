#!/usr/bin/env python3
"""
Validate Sha Empirical Estimates - BSD ∞³ Framework

Command-line script for running empirical Sha estimation validation
for elliptic curves with rank >= 2.

This script implements the SABIO ∞³ validation protocol for extended
empirical BSD verification.

Usage:
    python validate_sha_empirical.py [OPTIONS]
    
Examples:
    # Run default validation (500 curves, E_10001 to E_10500)
    python validate_sha_empirical.py
    
    # Run with custom parameters
    python validate_sha_empirical.py --num-curves 100 --start 20001 --seed 42
    
    # Export results to specific directory
    python validate_sha_empirical.py --output results/sha_validation/
    
    # Generate summary only (no file export)
    python validate_sha_empirical.py --summary-only

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: November 2025
License: MIT
"""

import argparse
import importlib.util
import sys
from datetime import datetime
from pathlib import Path

# Ensure the project root is in the path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))


def _load_sha_estimator_module():
    """Load sha_empirical_estimator module directly to avoid Sage dependency."""
    module_path = project_root / 'src' / 'verification' / 'sha_empirical_estimator.py'
    spec = importlib.util.spec_from_file_location("sha_empirical_estimator", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='BSD ∞³ - Sha Empirical Estimation Validation',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Run default validation (500 curves, E_10001 to E_10500)
  python validate_sha_empirical.py
  
  # Run with custom curve count
  python validate_sha_empirical.py --num-curves 100
  
  # Custom start index
  python validate_sha_empirical.py --start 20001 --num-curves 200
  
  # Export to specific directory with fixed seed
  python validate_sha_empirical.py --output results/ --seed 42
  
  # Summary mode (no file export)
  python validate_sha_empirical.py --summary-only

The script estimates |Sha(E)| using the simplified BSD formula:
  |Sha| ≈ (L'(E,1) * |T|²) / (R * Ω)
        """
    )
    
    parser.add_argument(
        '--num-curves', '-n',
        type=int,
        default=500,
        help='Number of synthetic curves to simulate (default: 500). '
             'Note: This generates random simulated data, not real curve analysis.'
    )
    
    parser.add_argument(
        '--start', '-s',
        type=int,
        default=10001,
        help='Starting curve index (default: 10001)'
    )
    
    parser.add_argument(
        '--seed',
        type=int,
        default=None,
        help='Random seed for reproducibility (default: None)'
    )
    
    parser.add_argument(
        '--output', '-o',
        type=str,
        default=None,
        help='Output directory for results (default: none)'
    )
    
    parser.add_argument(
        '--summary-only',
        action='store_true',
        help='Only print summary statistics, do not export files'
    )
    
    parser.add_argument(
        '--quiet', '-q',
        action='store_true',
        help='Suppress verbose output'
    )
    
    parser.add_argument(
        '--format',
        choices=['csv', 'json', 'both'],
        default='both',
        help='Output format for exported files (default: both)'
    )
    
    parser.add_argument(
        '--show-head',
        type=int,
        default=5,
        help='Number of sample rows to display (default: 5)'
    )
    
    args = parser.parse_args()
    
    verbose = not args.quiet
    output_dir = None if args.summary_only else args.output
    
    if verbose:
        print()
        print("=" * 70)
        print("BSD ∞³ — Sha Empirical Estimation Validation")
        print("=" * 70)
        print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print()
        print("Parameters:")
        print(f"  Number of curves: {args.num_curves}")
        print(f"  Curve range: E_{args.start} to E_{args.start + args.num_curves - 1}")
        print(f"  Random seed: {args.seed if args.seed else 'random'}")
        if args.output and not args.summary_only:
            print(f"  Output directory: {args.output}")
        print()
    
    try:
        # Load module
        sha_module = _load_sha_estimator_module()
        ShaEmpiricalEstimator = sha_module.ShaEmpiricalEstimator
        
        # Create estimator
        estimator = ShaEmpiricalEstimator(
            num_curves=args.num_curves,
            start_index=args.start,
            random_seed=args.seed
        )
        
        # Generate simulation
        df = estimator.generate_simulation()
        stats = estimator.get_statistics()
        
        if verbose:
            print(f"Simulation complete: {len(df)} curves generated")
            print()
            
            # Display sample
            print(f"Sample results (first {args.show_head} curves):")
            print("-" * 70)
            print(df.head(args.show_head).to_string(index=False))
            print()
            
            # Display statistics
            print("Statistics:")
            print("-" * 70)
            print(f"  Total curves: {stats['total_curves']}")
            print(f"  Rank distribution: {stats['rank_distribution']}")
            print()
            print("  Sha estimates:")
            print(f"    Mean:   {stats['sha_statistics']['mean']:.4f}")
            print(f"    Std:    {stats['sha_statistics']['std']:.4f}")
            print(f"    Min:    {stats['sha_statistics']['min']:.4f}")
            print(f"    Max:    {stats['sha_statistics']['max']:.4f}")
            print(f"    Median: {stats['sha_statistics']['median']:.4f}")
            print()
            print(f"  Curves with |Sha| > 1: {stats['curves_with_sha_gt_1']}")
            print(f"  Curves with |Sha| near perfect square: {stats['curves_with_sha_square']}")
            print()
            
            # Display by rank
            print("Breakdown by rank:")
            print("-" * 70)
            for rank in [2, 3, 4]:
                rank_df = estimator.get_by_rank(rank)
                if len(rank_df) > 0:
                    rank_sha_mean = rank_df["ShaEstimate"].mean()
                    rank_sha_std = rank_df["ShaEstimate"].std()
                    print(f"  Rank {rank}: {len(rank_df)} curves, "
                          f"Sha mean={rank_sha_mean:.4f}, std={rank_sha_std:.4f}")
            print()
        
        # Export results if output directory specified
        if output_dir:
            output_path = Path(output_dir)
            output_path.mkdir(parents=True, exist_ok=True)
            
            if verbose:
                print("Exporting results:")
                print("-" * 70)
            
            if args.format in ['csv', 'both']:
                csv_path = estimator.export_to_csv(output_path / "sha_estimates.csv")
                if verbose:
                    print(f"  CSV: {csv_path}")
            
            if args.format in ['json', 'both']:
                json_path = estimator.export_to_json(output_path / "sha_validation.json")
                if verbose:
                    print(f"  JSON: {json_path}")
            
            # Always save certificate
            import json
            cert = estimator.generate_certificate()
            cert_path = output_path / "sha_validation_certificate.json"
            with open(cert_path, 'w') as f:
                json.dump(cert, f, indent=2)
            if verbose:
                print(f"  Certificate: {cert_path}")
            
            print()
        
        if verbose:
            print("=" * 70)
            print("✅ Validation complete")
            print("=" * 70)
        
        return 0
        
    except Exception as e:
        print(f"❌ Error: {e}", file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
