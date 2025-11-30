#!/usr/bin/env python3
"""
BSD Curve Simulator - Simulated Elliptic Curve Data Generator

This module generates simulated data for elliptic curves with BSD conjecture
parameters. Useful for testing patterns, validating against LMFDB data, and
working with large-scale datasets for analysis.

The simulator creates realistic curve data including:
- Curve identifiers (Cremona-style labels)
- Conductors
- Analytic ranks
- Torsion orders
- L-derivative values at s=1
- Real periods
- Regulators
- Sha (Tate-Shafarevich group) estimates

The Sha estimate is computed using the BSD formula:
    |Ш| ≈ L'(E,1) / (Ω_E * Reg_E * |E(ℚ)_tors|²)
"""

import numpy as np
import pandas as pd
from typing import Optional, List, Dict, Any, Tuple


def generate_curve_label(seed: Optional[int] = None) -> str:
    """
    Generate a Cremona-style curve label.

    Generates labels of the form "NXn" where:
    - N is a conductor number (11-999)
    - X is a letter a-z indicating the isogeny class
    - n is a number 1-5 within the isogeny class

    Args:
        seed: Optional random seed for reproducibility

    Returns:
        str: A Cremona-style label like "11a1", "37b2", etc.

    Examples:
        >>> label = generate_curve_label(42)
        >>> isinstance(label, str)
        True
        >>> len(label) >= 4  # At least "NNaN"
        True
    """
    if seed is not None:
        np.random.seed(seed)

    letters = "abcdefghijklmnopqrstuvwxyz"
    conductor = np.random.randint(11, 1000)
    isogeny_class = np.random.choice(list(letters))
    curve_number = np.random.randint(1, 6)

    return f"{conductor}{isogeny_class}{curve_number}"


def generate_bsd_dataset(
    n_curves: int = 10000,
    random_seed: Optional[int] = None,
    conductor_range: Tuple[int, int] = (11, 10**6),
    rank_distribution: Optional[Dict[int, float]] = None,
    torsion_orders: Optional[List[int]] = None,
    include_metadata: bool = False
) -> pd.DataFrame:
    """
    Generate a simulated dataset of elliptic curves with BSD parameters.

    Creates a dataset with simulated curve data following realistic
    distributions for BSD conjecture-related parameters.

    Args:
        n_curves: Number of curves to generate (default: 10000)
        random_seed: Optional seed for reproducibility (default: None)
        conductor_range: Tuple of (min, max) conductor values
        rank_distribution: Dict mapping ranks to probabilities.
            Default: {0: 0.3, 1: 0.4, 2: 0.2, 3: 0.1}
        torsion_orders: List of possible torsion orders.
            Default: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        include_metadata: Whether to include additional metadata columns

    Returns:
        pd.DataFrame: DataFrame with columns:
            - curve_id: Cremona-style label
            - conductor: Conductor of the curve
            - analytic_rank: Analytic rank r such that ord_{s=1}L(E,s) = r
            - torsion_order: Order of the torsion subgroup |E(ℚ)_tors|
            - L_derivative_E1: L^(r)(E,1)/r! value
            - real_period: Real period Ω_E
            - regulator: Regulator Reg_E
            - sha_estimate: Estimated |Ш| from BSD formula

    Examples:
        >>> df = generate_bsd_dataset(n_curves=100, random_seed=42)
        >>> len(df)
        100
        >>> 'sha_estimate' in df.columns
        True
        >>> df['sha_estimate'].min() >= 0
        True
    """
    if random_seed is not None:
        np.random.seed(random_seed)

    # Default rank distribution
    if rank_distribution is None:
        rank_distribution = {0: 0.3, 1: 0.4, 2: 0.2, 3: 0.1}

    # Default torsion orders (based on Mazur's theorem)
    if torsion_orders is None:
        torsion_orders = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

    # Validate inputs
    if n_curves <= 0:
        raise ValueError("n_curves must be positive")
    if conductor_range[0] < 1 or conductor_range[1] <= conductor_range[0]:
        raise ValueError("Invalid conductor_range")

    # Normalize rank probabilities
    ranks = list(rank_distribution.keys())
    probs = list(rank_distribution.values())
    total_prob = sum(probs)
    probs = [p / total_prob for p in probs]

    # Generate curve labels
    labels = [generate_curve_label() for _ in range(n_curves)]

    # Generate conductors
    conductors = np.random.randint(
        conductor_range[0],
        conductor_range[1],
        size=n_curves
    )

    # Generate analytic ranks
    analytic_ranks = np.random.choice(ranks, size=n_curves, p=probs)

    # Generate torsion orders
    torsion = np.random.choice(torsion_orders, size=n_curves)

    # Generate L-derivative values (positive values)
    L_derivatives = np.round(
        np.random.uniform(0.001, 2.5, size=n_curves),
        5
    )

    # Generate real periods (positive values)
    real_periods = np.round(
        np.random.uniform(0.1, 5.0, size=n_curves),
        5
    )

    # Generate regulators (positive values, 1 for rank 0)
    regulators = np.round(
        np.random.uniform(0.01, 3.0, size=n_curves),
        5
    )
    # For rank 0 curves, regulator should be 1
    regulators = np.where(analytic_ranks == 0, 1.0, regulators)

    # Compute Sha estimates using BSD formula:
    # |Ш| ≈ L^(r)(E,1)/r! / (Ω_E * Reg_E * |E(ℚ)_tors|²)
    torsion_squared = torsion ** 2
    sha_estimates = L_derivatives / (
        real_periods * regulators * torsion_squared
    )
    sha_estimates = np.round(sha_estimates, 5)
    # Ensure sha_estimate is always strictly positive (BSD predicts |Ш| ≥ 1)
    sha_estimates = np.maximum(sha_estimates, 1e-5)

    # Create DataFrame
    data = {
        "curve_id": labels,
        "conductor": conductors,
        "analytic_rank": analytic_ranks,
        "torsion_order": torsion,
        "L_derivative_E1": L_derivatives,
        "real_period": real_periods,
        "regulator": regulators,
        "sha_estimate": sha_estimates,
    }

    df = pd.DataFrame(data)

    # Add optional metadata
    if include_metadata:
        df["simulation_seed"] = random_seed
        df["conductor_min"] = conductor_range[0]
        df["conductor_max"] = conductor_range[1]

    return df


def filter_by_rank(
    df: pd.DataFrame,
    ranks: List[int]
) -> pd.DataFrame:
    """
    Filter dataset to include only curves of specified ranks.

    Args:
        df: DataFrame generated by generate_bsd_dataset
        ranks: List of ranks to include

    Returns:
        pd.DataFrame: Filtered DataFrame

    Examples:
        >>> df = generate_bsd_dataset(100, random_seed=42)
        >>> high_rank = filter_by_rank(df, [2, 3])
        >>> all(high_rank['analytic_rank'].isin([2, 3]))
        True
    """
    return df[df['analytic_rank'].isin(ranks)].copy()


def get_sha_statistics(df: pd.DataFrame) -> Dict[str, Any]:
    """
    Compute statistics on Sha estimates grouped by rank.

    Args:
        df: DataFrame generated by generate_bsd_dataset

    Returns:
        dict: Statistics including:
            - overall: Overall statistics
            - by_rank: Statistics grouped by analytic rank

    Examples:
        >>> df = generate_bsd_dataset(100, random_seed=42)
        >>> stats = get_sha_statistics(df)
        >>> 'overall' in stats
        True
        >>> 'by_rank' in stats
        True
    """
    overall_stats = {
        "count": len(df),
        "mean": float(df['sha_estimate'].mean()),
        "std": float(df['sha_estimate'].std()),
        "min": float(df['sha_estimate'].min()),
        "max": float(df['sha_estimate'].max()),
        "median": float(df['sha_estimate'].median()),
    }

    by_rank = {}
    for rank in df['analytic_rank'].unique():
        rank_df = df[df['analytic_rank'] == rank]
        by_rank[int(rank)] = {
            "count": len(rank_df),
            "mean": float(rank_df['sha_estimate'].mean()),
            "std": float(rank_df['sha_estimate'].std()),
            "min": float(rank_df['sha_estimate'].min()),
            "max": float(rank_df['sha_estimate'].max()),
        }

    return {
        "overall": overall_stats,
        "by_rank": by_rank,
    }


def export_to_csv(
    df: pd.DataFrame,
    filepath: str,
    include_index: bool = False
) -> None:
    """
    Export the simulated dataset to a CSV file.

    Args:
        df: DataFrame to export
        filepath: Path to output CSV file
        include_index: Whether to include the DataFrame index

    Examples:
        >>> df = generate_bsd_dataset(10, random_seed=42)
        >>> export_to_csv(df, '/tmp/test_export.csv')
    """
    df.to_csv(filepath, index=include_index)


def export_to_latex(
    df: pd.DataFrame,
    filepath: str,
    caption: str = "BSD Simulated Curves",
    max_rows: int = 50
) -> None:
    """
    Export the simulated dataset to a LaTeX table.

    Args:
        df: DataFrame to export
        filepath: Path to output .tex file
        caption: Table caption
        max_rows: Maximum number of rows to include

    Examples:
        >>> df = generate_bsd_dataset(10, random_seed=42)
        >>> export_to_latex(df, '/tmp/test_export.tex')
    """
    subset = df.head(max_rows)

    latex_content = subset.to_latex(
        index=False,
        caption=caption,
        label="tab:bsd_curves",
        column_format="l" + "r" * (len(df.columns) - 1),
        float_format="%.5f"
    )

    with open(filepath, 'w') as f:
        f.write(latex_content)


def validate_bsd_consistency(df: pd.DataFrame) -> Dict[str, Any]:
    """
    Validate that the simulated data is consistent with BSD expectations.

    Checks:
    - All Sha estimates are positive
    - Regulators are 1 for rank 0 curves
    - All periods are positive
    - All L-derivative values are positive

    Args:
        df: DataFrame to validate

    Returns:
        dict: Validation results with pass/fail for each check

    Examples:
        >>> df = generate_bsd_dataset(100, random_seed=42)
        >>> validation = validate_bsd_consistency(df)
        >>> validation['all_valid']
        True
    """
    checks = {}

    # Check 1: All Sha estimates positive
    checks['sha_positive'] = bool((df['sha_estimate'] > 0).all())

    # Check 2: Regulators are 1 for rank 0
    rank_0 = df[df['analytic_rank'] == 0]
    if len(rank_0) > 0:
        checks['regulator_rank0'] = bool(
            np.allclose(rank_0['regulator'], 1.0)
        )
    else:
        checks['regulator_rank0'] = True  # No rank 0 curves to check

    # Check 3: All periods positive
    checks['periods_positive'] = bool((df['real_period'] > 0).all())

    # Check 4: All L-derivatives positive
    checks['L_derivatives_positive'] = bool((df['L_derivative_E1'] > 0).all())

    # Check 5: All torsion orders are positive integers
    checks['torsion_valid'] = bool(
        (df['torsion_order'] > 0).all() and
        (df['torsion_order'] == df['torsion_order'].astype(int)).all()
    )

    # Check 6: All conductors are positive
    checks['conductors_positive'] = bool((df['conductor'] > 0).all())

    checks['all_valid'] = all(checks.values())

    return checks


def quick_demo(n_curves: int = 5) -> pd.DataFrame:
    """
    Run a quick demonstration of the simulator.

    Args:
        n_curves: Number of curves to generate

    Returns:
        pd.DataFrame: Generated dataset

    Examples:
        >>> df = quick_demo(3)
        >>> len(df)
        3
    """
    print("=" * 70)
    print("BSD CURVE SIMULATOR - QUICK DEMO")
    print("=" * 70)

    df = generate_bsd_dataset(n_curves=n_curves, random_seed=42)

    print(f"\nGenerated {len(df)} simulated elliptic curves\n")
    print(df.to_string(index=False))
    print()

    stats = get_sha_statistics(df)
    print("Sha Estimate Statistics:")
    print(f"  Mean: {stats['overall']['mean']:.5f}")
    print(f"  Std:  {stats['overall']['std']:.5f}")
    print(f"  Min:  {stats['overall']['min']:.5f}")
    print(f"  Max:  {stats['overall']['max']:.5f}")

    validation = validate_bsd_consistency(df)
    print(f"\nValidation: {'PASSED' if validation['all_valid'] else 'FAILED'}")

    print("=" * 70)

    return df


# Main execution
if __name__ == "__main__":
    # Run demonstration with 10,000 curves (as in problem statement)
    print("\n🔬 BSD Curve Simulator - Full Demo")
    print("Generating 10,000 simulated elliptic curves...\n")

    df = generate_bsd_dataset(n_curves=10000, random_seed=42)

    print("Dataset Preview (first 5 rows):")
    print(df.head().to_string(index=False))
    print()

    print("Dataset Summary:")
    print(f"  Total curves: {len(df)}")
    print("  Rank distribution:")
    for rank, count in df['analytic_rank'].value_counts().sort_index().items():
        print(f"    Rank {rank}: {count} ({count/len(df)*100:.1f}%)")

    print()
    stats = get_sha_statistics(df)
    print("Sha Estimate Statistics by Rank:")
    for rank in sorted(stats['by_rank'].keys()):
        s = stats['by_rank'][rank]
        print(f"  Rank {rank}: mean={s['mean']:.5f}, std={s['std']:.5f}")

    validation = validate_bsd_consistency(df)
    print(f"\nValidation: {'✓ PASSED' if validation['all_valid'] else '✗ FAILED'}")
