#!/usr/bin/env python3
"""
BSD Simulation Demo - Demonstrates the BSD Curve Simulator

This demo shows how to use the bsd_curve_simulator module to generate
simulated elliptic curve data for BSD conjecture analysis.

Usage:
    python examples/bsd_simulation_demo.py
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from src.bsd_curve_simulator import (
    generate_bsd_dataset,
    filter_by_rank,
    get_sha_statistics,
    validate_bsd_consistency,
    export_to_csv,
    quick_demo
)


def main():
    """Main demo function"""
    print("=" * 70)
    print("BSD CURVE SIMULATOR DEMO")
    print("Simulating Elliptic Curve Data for BSD Conjecture Analysis")
    print("=" * 70)
    print()

    # Demo 1: Quick demo with small dataset
    print("📋 DEMO 1: Quick Demo (5 curves)")
    print("-" * 50)
    quick_demo(5)
    print()

    # Demo 2: Generate 10,000 curves (as in problem statement)
    print("📋 DEMO 2: Large-Scale Simulation (10,000 curves)")
    print("-" * 50)

    df = generate_bsd_dataset(
        n_curves=10000,
        random_seed=42,
        conductor_range=(11, 10**6),
        rank_distribution={0: 0.3, 1: 0.4, 2: 0.2, 3: 0.1}
    )

    print(f"Generated {len(df)} simulated elliptic curves")
    print()

    # Display first 5 rows
    print("First 5 curves:")
    print(df.head().to_string(index=False))
    print()

    # Display rank distribution
    print("Rank Distribution:")
    for rank in sorted(df['analytic_rank'].unique()):
        count = (df['analytic_rank'] == rank).sum()
        pct = count / len(df) * 100
        print(f"  Rank {rank}: {count} curves ({pct:.1f}%)")
    print()

    # Demo 3: Filter high-rank curves
    print("📋 DEMO 3: Filter High-Rank Curves (rank ≥ 2)")
    print("-" * 50)

    high_rank = filter_by_rank(df, [2, 3])
    print(f"Found {len(high_rank)} curves with rank ≥ 2")
    print()
    print("Sample high-rank curves:")
    print(high_rank.head().to_string(index=False))
    print()

    # Demo 4: Sha statistics
    print("📋 DEMO 4: Sha Statistics")
    print("-" * 50)

    stats = get_sha_statistics(df)

    print("Overall Sha Statistics:")
    print(f"  Count:  {stats['overall']['count']}")
    print(f"  Mean:   {stats['overall']['mean']:.5f}")
    print(f"  Std:    {stats['overall']['std']:.5f}")
    print(f"  Min:    {stats['overall']['min']:.5f}")
    print(f"  Max:    {stats['overall']['max']:.5f}")
    print(f"  Median: {stats['overall']['median']:.5f}")
    print()

    print("Sha Statistics by Rank:")
    for rank in sorted(stats['by_rank'].keys()):
        s = stats['by_rank'][rank]
        print(f"  Rank {rank}: n={s['count']}, mean={s['mean']:.5f}, "
              f"std={s['std']:.5f}")
    print()

    # Demo 5: Validation
    print("📋 DEMO 5: Data Validation")
    print("-" * 50)

    validation = validate_bsd_consistency(df)

    print("Validation Results:")
    for check, passed in validation.items():
        if check != 'all_valid':
            status = "✓ PASSED" if passed else "✗ FAILED"
            print(f"  {check}: {status}")

    overall = "✓ ALL CHECKS PASSED" if validation['all_valid'] else "✗ SOME CHECKS FAILED"
    print(f"\nOverall: {overall}")
    print()

    # Demo 6: Export (optional)
    print("📋 DEMO 6: Export Options")
    print("-" * 50)
    print("Available export functions:")
    print("  - export_to_csv(df, 'curves.csv')")
    print("  - export_to_latex(df, 'curves.tex')")
    print()

    # Example export to /tmp for demonstration
    export_path = "/tmp/bsd_simulated_curves.csv"
    export_to_csv(df, export_path)
    print(f"✓ Exported dataset to: {export_path}")
    print()

    print("=" * 70)
    print("DEMO COMPLETE")
    print("=" * 70)

    return df


if __name__ == "__main__":
    main()
