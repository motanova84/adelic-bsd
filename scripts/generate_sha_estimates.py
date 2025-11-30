#!/usr/bin/env python3
"""
SHA Estimates Generator for Rank ≥ 2 Curves

Generates simulated elliptic curve data with SHA (Tate-Shafarevich group)
estimates using the simplified BSD formula:

    sha_estimate = (L'(E,1) · period) / (regulator · torsion²)

This data is for validation and testing purposes in the adelic-bsd framework.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: November 2025
License: MIT
"""

import argparse
from pathlib import Path

import numpy as np
import pandas as pd


def generate_sha_estimates(
    num_curves: int = 5000,
    seed: int = 42,
    output_path: str | None = None
) -> pd.DataFrame:
    """
    Generate simulated elliptic curve data with SHA estimates.

    Parameters
    ----------
    num_curves : int
        Number of curves to generate (default: 5000)
    seed : int
        Random seed for reproducibility (default: 42)
    output_path : str, optional
        Path to save CSV file. If None, returns DataFrame without saving.

    Returns
    -------
    pd.DataFrame
        DataFrame with columns:
        - curve_id: Unique identifier (E_5001, E_5002, ...)
        - rank: Algebraic rank (2, 3, or 4)
        - conductor: Conductor between 100,000 and 800,000
        - torsion_order: Order of torsion subgroup (1, 2, 4, or 6)
        - regulator: Regulator value (1.0 to 50.0)
        - period: Real period (0.1 to 10.0)
        - ls_deriv: L-series derivative L'(E,1) (0.01 to 2.0)
        - sha_estimate: Estimated |Sha| using simplified BSD formula
    """
    np.random.seed(seed)

    # Generate curve data
    data = {
        "curve_id": [f"E_{5001 + i}" for i in range(num_curves)],
        "rank": np.random.choice([2, 3, 4], size=num_curves, p=[0.7, 0.25, 0.05]),
        "conductor": np.random.randint(100000, 800000, size=num_curves),
        "torsion_order": np.random.choice([1, 2, 4, 6], size=num_curves),
        "regulator": np.round(np.random.uniform(1.0, 50.0, size=num_curves), 4),
        "period": np.round(np.random.uniform(0.1, 10.0, size=num_curves), 4),
        "ls_deriv": np.round(np.random.uniform(0.01, 2.0, size=num_curves), 6),
    }

    # Calculate SHA estimate using simplified BSD formula
    # sha_estimate = (L'(E,1) * Period) / (Regulator * Torsion^2)
    torsion_squared = np.square(data["torsion_order"])
    sha_estimate = (data["ls_deriv"] * data["period"]) / (
        data["regulator"] * torsion_squared
    )
    # Use 8 decimal places to preserve small values
    data["sha_estimate"] = np.round(sha_estimate, 8)

    df = pd.DataFrame(data)

    # Save to CSV if output path provided
    if output_path:
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        df.to_csv(output_path, index=False)
        print(f"✅ Generated {num_curves} curves with SHA estimates")
        print(f"📄 Saved to: {output_path}")

    return df


def validate_sha_estimates(df: pd.DataFrame) -> dict:
    """
    Validate the generated SHA estimates data.

    Parameters
    ----------
    df : pd.DataFrame
        DataFrame with SHA estimates

    Returns
    -------
    dict
        Validation results with checks and statistics
    """
    required_columns = [
        "curve_id",
        "rank",
        "conductor",
        "torsion_order",
        "regulator",
        "period",
        "ls_deriv",
        "sha_estimate",
    ]

    has_required_columns = all(col in df.columns for col in required_columns)

    # Only perform column-specific checks if columns exist
    checks = {
        "has_required_columns": has_required_columns,
        "all_ranks_geq_2": (df["rank"] >= 2).all() if "rank" in df.columns else False,
        "all_sha_positive": (
            (df["sha_estimate"] > 0).all() if "sha_estimate" in df.columns else False
        ),
        "all_regulator_positive": (
            (df["regulator"] > 0).all() if "regulator" in df.columns else False
        ),
        "all_period_positive": (
            (df["period"] > 0).all() if "period" in df.columns else False
        ),
        "conductor_in_range": (
            ((df["conductor"] >= 100000) & (df["conductor"] <= 800000)).all()
            if "conductor" in df.columns
            else False
        ),
        "no_missing_values": not df.isnull().any().any(),
    }

    stats = {}
    if has_required_columns:
        stats = {
            "total_curves": len(df),
            "rank_distribution": df["rank"].value_counts().to_dict(),
            "torsion_distribution": df["torsion_order"].value_counts().to_dict(),
            "sha_estimate_stats": {
                "min": float(df["sha_estimate"].min()),
                "max": float(df["sha_estimate"].max()),
                "mean": float(df["sha_estimate"].mean()),
                "median": float(df["sha_estimate"].median()),
            },
        }
    else:
        stats = {
            "total_curves": len(df),
            "error": "Missing required columns",
        }

    return {
        "all_checks_passed": all(checks.values()),
        "checks": checks,
        "statistics": stats,
    }


def main():
    """Main entry point for CLI usage."""
    parser = argparse.ArgumentParser(
        description="Generate SHA estimates for rank ≥ 2 elliptic curves",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Generate default 5000 curves and save to data/rank2plus/sha_estimates.csv
  python generate_sha_estimates.py

  # Generate custom number of curves
  python generate_sha_estimates.py --num-curves 10000

  # Use different seed for different random data
  python generate_sha_estimates.py --seed 123

  # Validate existing data
  python generate_sha_estimates.py --validate-only
        """,
    )

    parser.add_argument(
        "--num-curves",
        "-n",
        type=int,
        default=5000,
        help="Number of curves to generate (default: 5000)",
    )
    parser.add_argument(
        "--seed",
        "-s",
        type=int,
        default=42,
        help="Random seed for reproducibility (default: 42)",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=str,
        default=None,
        help="Output path for CSV file (default: data/rank2plus/sha_estimates.csv)",
    )
    parser.add_argument(
        "--validate-only",
        "-v",
        action="store_true",
        help="Only validate existing data, don't generate new",
    )

    args = parser.parse_args()

    # Determine output path
    if args.output:
        output_path = Path(args.output)
    else:
        # Default path relative to script location
        script_dir = Path(__file__).parent.parent
        output_path = script_dir / "data" / "rank2plus" / "sha_estimates.csv"

    if args.validate_only:
        # Validate existing data
        if not output_path.exists():
            print(f"❌ Error: {output_path} does not exist")
            return 1

        df = pd.read_csv(output_path)
        results = validate_sha_estimates(df)

        print(f"\n📊 Validation Results for {output_path}")
        print("=" * 60)

        for check_name, passed in results["checks"].items():
            status = "✅" if passed else "❌"
            print(f"  {status} {check_name}")

        print("\n📈 Statistics:")
        print(f"  Total curves: {results['statistics']['total_curves']}")
        print(f"  Rank distribution: {results['statistics']['rank_distribution']}")
        sha_stats = results["statistics"]["sha_estimate_stats"]
        print(f"  SHA estimate range: [{sha_stats['min']:.5f}, {sha_stats['max']:.5f}]")
        print(f"  SHA estimate mean: {sha_stats['mean']:.5f}")

        return 0 if results["all_checks_passed"] else 1

    # Generate data
    df = generate_sha_estimates(
        num_curves=args.num_curves,
        seed=args.seed,
        output_path=output_path,
    )

    # Run validation
    results = validate_sha_estimates(df)

    print("\n📊 Validation:")
    for check_name, passed in results["checks"].items():
        status = "✅" if passed else "❌"
        print(f"  {status} {check_name}")

    return 0 if results["all_checks_passed"] else 1


if __name__ == "__main__":
    exit(main())
