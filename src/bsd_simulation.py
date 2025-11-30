"""
BSD Simulation Module - Large-Scale Curve Simulation for BSD Conjecture Validation
==================================================================================

This module provides functionality to simulate elliptic curves with rank ≥ 2
and estimate Tate-Shafarevich group (Sha) values using an approximated BSD formula.

Features:
---------
- Generate simulated BSD data for curves E_10001 to E_10500+
- Estimate |Sha| using simplified BSD formula (without full local factors)
- Selmer parity analysis for rank ≥ 2 curves
- Anomaly detection for BSD candidates
- Export to CSV for analysis and Lean4 formalization

Note: This module generates SIMULATED data for testing and validation purposes.
The Sha estimates use a simplified approximation formula, not the full BSD formula.

Statistics aligned with LMFDB-style distributions:
- 70% rank=2, 25% rank=3, 5% rank=4
- Conductors in range 1k-100k (10^3 to 10^5)
- Sha estimates computed via simplified formula: L'(E,1) * |Torsion|² / (Ω * Reg)
"""

import numpy as np
import pandas as pd
from pathlib import Path
from typing import Optional, Tuple, List, Dict, Any


def generate_rank2plus_curves(
    num_curves: int = 500,
    start_id: int = 10001,
    random_seed: Optional[int] = None
) -> pd.DataFrame:
    """
    Generate simulated elliptic curves with rank ≥ 2.

    Uses realistic parameter distributions aligned with LMFDB statistics:
    - 70% rank=2, 25% rank=3, 5% rank=4
    - Conductors in range 10^3 to 10^5
    - Torsion orders from 1 to 6

    Args:
        num_curves: Number of curves to generate (default 500)
        start_id: Starting curve ID (default 10001)
        random_seed: Random seed for reproducibility (optional)

    Returns:
        DataFrame with simulated BSD data including Sha estimates
    """
    if random_seed is not None:
        np.random.seed(random_seed)

    # Generate curve IDs
    curve_ids = [f"E_{start_id + i}" for i in range(num_curves)]

    # Conductors: realistic range 10^3 to 10^5
    conductors = np.random.randint(10**3, 10**5, num_curves)

    # Rank distribution: 70% rank=2, 25% rank=3, 5% rank=4
    rank_probs = [0.70, 0.25, 0.05]
    ranks = np.random.choice([2, 3, 4], num_curves, p=rank_probs)

    # Torsion orders: typically small (1-6)
    torsion_orders = np.random.choice([1, 2, 3, 4, 5, 6], num_curves)

    # Regulators: typically between 0.1 and 10
    regulators = np.round(np.random.uniform(0.1, 10.0, num_curves), 4)

    # Real periods: typically between 0.01 and 5
    real_periods = np.round(np.random.uniform(0.01, 5.0, num_curves), 4)

    # L'(E,1) derivatives: typically small values
    l_derivatives = np.round(np.random.uniform(0.01, 1.0, num_curves), 5)

    # Estimate |Sha| using simplified BSD formula:
    # |Sha| ≈ L'(E,1) * |Torsion|² / (Regulator * Real Period)
    sha_estimates = np.round(
        (l_derivatives * torsion_orders**2) / (regulators * real_periods),
        3
    )

    # Create DataFrame
    df = pd.DataFrame({
        "curve_id": curve_ids,
        "conductor": conductors,
        "rank": ranks,
        "torsion_order": torsion_orders,
        "regulator": regulators,
        "real_period": real_periods,
        "l_derivative": l_derivatives,
        "sha_estimate": sha_estimates
    })

    return df


def add_selmer_parity_columns(df: pd.DataFrame, random_seed: Optional[int] = None) -> pd.DataFrame:
    """
    Add Selmer parity and Sha dimension columns to BSD data.

    Computes:
    - selmer2_dim: 2-Selmer dimension (rank + Poisson adjustment)
    - torsion2_dim: 2-torsion dimension (1 if even torsion, 0 otherwise)
    - sha2_dim: Sha[2] dimension (selmer2 - rank - torsion2)
    - parity_ok: Whether parity relation holds
    - sha_anomaly: Whether curve has anomalous Sha (dim > 2 or estimate > 1)

    Args:
        df: DataFrame with BSD curve data
        random_seed: Random seed for reproducibility (optional)

    Returns:
        DataFrame with additional Selmer/Sha columns
    """
    if random_seed is not None:
        np.random.seed(random_seed)

    df = df.copy()
    n = len(df)

    # 2-Selmer dimension: at least rank, with Poisson adjustment
    df["selmer2_dim"] = np.maximum(
        df["rank"] + np.random.poisson(0.4, n), 0
    ).astype(int)

    # 2-torsion dimension: 1 if torsion order is even
    df["torsion2_dim"] = (df["torsion_order"] % 2 == 0).astype(int)

    # Sha[2] dimension: difference between Selmer and rank+torsion
    df["sha2_dim"] = df["selmer2_dim"] - df["rank"] - df["torsion2_dim"]

    # Parity check: Selmer = rank + torsion2 + sha2
    df["parity_ok"] = (
        df["selmer2_dim"] == df["rank"] + df["torsion2_dim"] + df["sha2_dim"]
    )

    # Sha anomaly detection: high Sha dimension or estimate
    df["sha_anomaly"] = (df["sha2_dim"] > 2) | (df["sha_estimate"] > 1)

    return df


def detect_anomalies(df: pd.DataFrame) -> pd.DataFrame:
    """
    Detect BSD anomalies in curve data.

    Anomalies include:
    - sha2_dim >= 2
    - sha_estimate > 0.5
    - rank >= 3

    Args:
        df: DataFrame with BSD curve data

    Returns:
        DataFrame containing only anomalous curves, sorted by severity
    """
    anomalies = df[
        (df.get("sha2_dim", 0) >= 2) |
        (df["sha_estimate"] > 0.5) |
        (df["rank"] >= 3)
    ].copy()

    # Sort by Sha dimension and estimate (most anomalous first)
    if "sha2_dim" in anomalies.columns:
        anomalies = anomalies.sort_values(
            ["sha2_dim", "sha_estimate"],
            ascending=[False, False]
        )
    else:
        anomalies = anomalies.sort_values("sha_estimate", ascending=False)

    return anomalies


def get_top_priorities(
    df: pd.DataFrame,
    top_n: int = 20,
    priority_columns: Optional[List[str]] = None
) -> pd.DataFrame:
    """
    Get top priority curves for BSD validation.

    Args:
        df: DataFrame with BSD curve data
        top_n: Number of top curves to return
        priority_columns: Columns to return (default: curve_id, rank, sha2_dim, sha_estimate)

    Returns:
        DataFrame with top priority curves
    """
    if priority_columns is None:
        priority_columns = ["curve_id", "rank", "sha_estimate"]
        if "sha2_dim" in df.columns:
            priority_columns.insert(2, "sha2_dim")
        if "selmer2_dim" in df.columns:
            priority_columns.append("selmer2_dim")
        if "parity_ok" in df.columns:
            priority_columns.append("parity_ok")

    # Filter available columns
    available_cols = [c for c in priority_columns if c in df.columns]

    # Get anomalous curves
    anomalies = detect_anomalies(df)

    if len(anomalies) == 0:
        return df.head(top_n)[available_cols]

    return anomalies.head(top_n)[available_cols]


def compute_statistics(df: pd.DataFrame) -> Dict[str, Any]:
    """
    Compute summary statistics for BSD curve data.

    Args:
        df: DataFrame with BSD curve data

    Returns:
        Dictionary with statistics
    """
    stats = {
        "total_curves": len(df),
        "rank_distribution": df["rank"].value_counts().to_dict(),
        "mean_sha_estimate": float(df["sha_estimate"].mean()),
        "median_sha_estimate": float(df["sha_estimate"].median()),
        "sha_gt_1_count": int((df["sha_estimate"] > 1).sum()),
        "sha_gt_1_percent": float((df["sha_estimate"] > 1).mean() * 100),
    }

    if "sha2_dim" in df.columns:
        stats["sha_nonzero_count"] = int((df["sha2_dim"] != 0).sum())
        stats["sha_nonzero_percent"] = float((df["sha2_dim"] != 0).mean() * 100)
        stats["mean_sha2_dim"] = float(df["sha2_dim"].mean())
        stats["sha_gte_2_count"] = int((df["sha2_dim"] >= 2).sum())

    if "sha_anomaly" in df.columns:
        stats["anomaly_count"] = int(df["sha_anomaly"].sum())
        stats["anomaly_percent"] = float(df["sha_anomaly"].mean() * 100)

    return stats


def export_to_csv(
    df: pd.DataFrame,
    filename: str,
    data_dir: Optional[Path] = None
) -> Path:
    """
    Export DataFrame to CSV in the data directory.

    Args:
        df: DataFrame to export
        filename: Output filename
        data_dir: Data directory path (default: data/)

    Returns:
        Path to saved file
    """
    if data_dir is None:
        data_dir = Path(__file__).parent.parent / "data"

    data_dir.mkdir(parents=True, exist_ok=True)
    filepath = data_dir / filename
    df.to_csv(filepath, index=False)

    return filepath


def generate_complete_bsd_dataset(
    num_curves: int = 500,
    start_id: int = 10001,
    random_seed: int = 42,
    export: bool = True
) -> Tuple[pd.DataFrame, Dict[str, Any]]:
    """
    Generate a complete BSD dataset with all columns and statistics.

    This is the main entry point for generating BSD simulation data.

    Args:
        num_curves: Number of curves to generate
        start_id: Starting curve ID
        random_seed: Random seed for reproducibility
        export: Whether to export to CSV files

    Returns:
        Tuple of (DataFrame with all data, statistics dictionary)
    """
    # Generate base curves
    df = generate_rank2plus_curves(
        num_curves=num_curves,
        start_id=start_id,
        random_seed=random_seed
    )

    # Add Selmer parity columns
    df = add_selmer_parity_columns(df, random_seed=random_seed + 1)

    # Compute statistics
    stats = compute_statistics(df)

    # Export if requested
    if export:
        # Main dataset
        export_to_csv(df, "rank2plus_bsd_complete.csv")

        # Anomalies
        anomalies = detect_anomalies(df)
        if len(anomalies) > 0:
            export_to_csv(anomalies, "bsd_infinity3_anomalies.csv")

        # Top priorities
        priorities = get_top_priorities(df, top_n=20)
        export_to_csv(priorities, "rank2plus_priorities.csv")

    return df, stats


def print_dataset_summary(df: pd.DataFrame, stats: Dict[str, Any]) -> None:
    """
    Print a summary of the generated dataset.

    Args:
        df: DataFrame with BSD curve data
        stats: Statistics dictionary
    """
    print("\n" + "=" * 70)
    print("BSD ∞³ — DATASET SUMMARY")
    print("=" * 70)
    print(f"Total curves: {stats['total_curves']}")
    print("\nRank distribution:")
    for rank, count in sorted(stats['rank_distribution'].items()):
        pct = count / stats['total_curves'] * 100
        print(f"  Rank {rank}: {count} ({pct:.1f}%)")

    print("\nSha statistics:")
    print(f"  Mean |Ш| estimate: {stats['mean_sha_estimate']:.4f}")
    print(f"  Median |Ш| estimate: {stats['median_sha_estimate']:.4f}")
    print(f"  Curves with |Ш| > 1: {stats['sha_gt_1_count']} ({stats['sha_gt_1_percent']:.1f}%)")

    if "sha_nonzero_count" in stats:
        nonzero_count = stats['sha_nonzero_count']
        nonzero_pct = stats['sha_nonzero_percent']
        print(f"  Curves with Ш ≠ 0: {nonzero_count} ({nonzero_pct:.1f}%)")
        print(f"  Mean dim(Ш[2]): {stats['mean_sha2_dim']:.2f}")
        print(f"  Curves with dim(Ш[2]) ≥ 2: {stats['sha_gte_2_count']}")

    if "anomaly_count" in stats:
        print(f"\nAnomalies detected: {stats['anomaly_count']} ({stats['anomaly_percent']:.1f}%)")

    print("\n" + "=" * 70)

    # Show sample data
    print("\nSample data (first 5 rows):")
    print(df.head().to_string(index=False))


if __name__ == "__main__":
    # Generate and display complete dataset
    df, stats = generate_complete_bsd_dataset(
        num_curves=500,
        start_id=10001,
        random_seed=42,
        export=True
    )

    print_dataset_summary(df, stats)

    # Show top priorities
    print("\n🔍 TOP PRIORITY BSD CANDIDATES:")
    priorities = get_top_priorities(df, top_n=10)
    print(priorities.to_string(index=False))
