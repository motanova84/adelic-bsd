#!/usr/bin/env python3
"""
SHA (Tate-Shafarevich) Group Estimation Analysis
=================================================

This script analyzes the global coherence of |Ш(E)| estimates for elliptic curves
with rank ≥ 2, detecting potential numerical anomalies and generating meaningful
visualizations.

Scientific Tasks:
- Group curves by rank (r = 2, r = 3, ...) and generate histograms
- Analyze correlations between log|Ш(E)|, log(R_E), and log(L^(r)(1))
- Detect outliers: curves with very large or small |Ш|
- Identify stability issues (regulators or L-derivatives near zero)

Deep Meaning:
These correlations evaluate the stability of the BSD formula in derivatives of
order r, and the plausibility that |Ш| values are integers or near-integers,
as expected if BSD is true.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
"""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt


def load_sha_estimates(csv_path):
    """
    Load SHA estimates from CSV file.

    Expected columns:
    - curve_label: LMFDB label
    - rank: algebraic rank of the curve
    - sha_estimate: estimated |Ш(E)|
    - R: regulator R_E
    - l_derivative: L^(r)(1) value
    - conductor: conductor N_E (optional)

    Args:
        csv_path: Path to the CSV file

    Returns:
        DataFrame with SHA estimates
    """
    df = pd.read_csv(csv_path)

    # Validate required columns
    required_cols = ['sha_estimate', 'R', 'l_derivative']
    missing = [c for c in required_cols if c not in df.columns]
    if missing:
        raise ValueError(f"Missing required columns: {missing}")

    return df


def compute_log_transforms(df):
    """
    Compute log-transforms for key quantities.

    Handles zero or negative values gracefully by replacing them
    with small positive values before taking logarithms.

    Args:
        df: DataFrame with SHA estimates

    Returns:
        DataFrame with additional log-transformed columns
    """
    # Replace zero/negative values with small epsilon for log safety
    epsilon = 1e-100

    df = df.copy()
    df["log_sha"] = np.log(np.maximum(df["sha_estimate"].abs(), epsilon))
    df["log_regulator"] = np.log(np.maximum(df["R"].abs(), epsilon))
    df["log_Lr"] = np.log(np.maximum(df["l_derivative"].abs(), epsilon))

    # Conductor if available
    if "conductor" in df.columns:
        df["log_conductor"] = np.log(np.maximum(df["conductor"], epsilon))

    return df


def generate_histogram(df, output_dir, by_rank=False):
    """
    Generate histograms of log(|Ш|) distribution.

    Args:
        df: DataFrame with log-transformed data
        output_dir: Directory to save output files
        by_rank: If True, generate separate histograms per rank
    """
    # Global histogram
    plt.figure(figsize=(10, 6))
    plt.hist(df["log_sha"], bins=50, edgecolor='black', alpha=0.7)
    plt.title("Distribución log(|Ш|) - Global")
    plt.xlabel("log(|Ш|)")
    plt.ylabel("Número de curvas")
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(output_dir / "log_sha_histogram.png", dpi=150)
    plt.close()
    print("✅ Saved: log_sha_histogram.png")

    # Histograms by rank if requested
    if by_rank and "rank" in df.columns:
        ranks = sorted(df["rank"].unique())
        for r in ranks:
            if r < 2:
                continue  # Focus on rank >= 2
            df_rank = df[df["rank"] == r]
            if len(df_rank) < 5:
                continue  # Skip if too few curves

            plt.figure(figsize=(10, 6))
            plt.hist(df_rank["log_sha"], bins=30, edgecolor='black', alpha=0.7)
            plt.title(f"Distribución log(|Ш|) - Rango {r}")
            plt.xlabel("log(|Ш|)")
            plt.ylabel("Número de curvas")
            plt.grid(True, alpha=0.3)
            plt.tight_layout()
            plt.savefig(output_dir / f"log_sha_histogram_rank{r}.png", dpi=150)
            plt.close()
            print(f"✅ Saved: log_sha_histogram_rank{r}.png")


def generate_correlation_plots(df, output_dir):
    """
    Generate scatter plots for key correlations.

    Correlations analyzed:
    - log(|Ш|) vs log(R_E)
    - log(|Ш|) vs log(L^(r)(1))
    - log(|Ш|) vs log(N_E) if conductor available

    Args:
        df: DataFrame with log-transformed data
        output_dir: Directory to save output files
    """
    # log(|Ш|) vs log(R)
    plt.figure(figsize=(10, 8))
    plt.scatter(df["log_regulator"], df["log_sha"], alpha=0.5, s=20)
    plt.title("log(|Ш|) vs log(R)")
    plt.xlabel("log(R)")
    plt.ylabel("log(|Ш|)")
    plt.grid(True, alpha=0.3)

    # Add correlation coefficient
    valid = ~(df["log_regulator"].isna() | df["log_sha"].isna())
    if valid.sum() > 2:
        corr = np.corrcoef(df.loc[valid, "log_regulator"],
                           df.loc[valid, "log_sha"])[0, 1]
        plt.annotate(f"Correlación: {corr:.4f}",
                     xy=(0.05, 0.95), xycoords='axes fraction',
                     fontsize=10, verticalalignment='top')

    plt.tight_layout()
    plt.savefig(output_dir / "log_sha_vs_logR.png", dpi=150)
    plt.close()
    print("✅ Saved: log_sha_vs_logR.png")

    # log(|Ш|) vs log(L^(r)(1))
    plt.figure(figsize=(10, 8))
    plt.scatter(df["log_Lr"], df["log_sha"], alpha=0.5, s=20)
    plt.title(r"log(|Ш|) vs log($L^{(r)}(1)$)")
    plt.xlabel(r"log($L^{(r)}(1)$)")
    plt.ylabel("log(|Ш|)")
    plt.grid(True, alpha=0.3)

    valid = ~(df["log_Lr"].isna() | df["log_sha"].isna())
    if valid.sum() > 2:
        corr = np.corrcoef(df.loc[valid, "log_Lr"],
                           df.loc[valid, "log_sha"])[0, 1]
        plt.annotate(f"Correlación: {corr:.4f}",
                     xy=(0.05, 0.95), xycoords='axes fraction',
                     fontsize=10, verticalalignment='top')

    plt.tight_layout()
    plt.savefig(output_dir / "log_sha_vs_logLr.png", dpi=150)
    plt.close()
    print("✅ Saved: log_sha_vs_logLr.png")

    # log(|Ш|) vs log(N_E) if conductor available
    if "log_conductor" in df.columns:
        plt.figure(figsize=(10, 8))
        plt.scatter(df["log_conductor"], df["log_sha"], alpha=0.5, s=20)
        plt.title("log(|Ш|) vs log(N_E)")
        plt.xlabel("log(N_E)")
        plt.ylabel("log(|Ш|)")
        plt.grid(True, alpha=0.3)

        valid = ~(df["log_conductor"].isna() | df["log_sha"].isna())
        if valid.sum() > 2:
            corr = np.corrcoef(df.loc[valid, "log_conductor"],
                               df.loc[valid, "log_sha"])[0, 1]
            plt.annotate(f"Correlación: {corr:.4f}",
                         xy=(0.05, 0.95), xycoords='axes fraction',
                         fontsize=10, verticalalignment='top')

        plt.tight_layout()
        plt.savefig(output_dir / "log_sha_vs_logN.png", dpi=150)
        plt.close()
        print("✅ Saved: log_sha_vs_logN.png")


def detect_outliers(df, threshold_sigma=3.0):
    """
    Detect curves with anomalous |Ш| values.

    Anomalies detected:
    - |Ш| very large (> mean + threshold * std)
    - |Ш| very small (< mean - threshold * std)
    - Regulator near zero (potential instability)
    - L-derivative near zero (potential instability)

    Args:
        df: DataFrame with log-transformed data
        threshold_sigma: Number of standard deviations for outlier detection

    Returns:
        Dictionary with outlier information
    """
    outliers = {
        'sha_high': [],
        'sha_low': [],
        'regulator_small': [],
        'l_derivative_small': []
    }

    # Statistical thresholds for log(|Ш|)
    mean_log_sha = df["log_sha"].mean()
    std_log_sha = df["log_sha"].std()

    high_thresh = mean_log_sha + threshold_sigma * std_log_sha
    low_thresh = mean_log_sha - threshold_sigma * std_log_sha

    # Find outliers
    for idx, row in df.iterrows():
        label = row.get('curve_label', f"curve_{idx}")

        # High |Ш| outliers
        if row["log_sha"] > high_thresh:
            outliers['sha_high'].append({
                'label': label,
                'sha_estimate': row['sha_estimate'],
                'log_sha': row['log_sha'],
                'z_score': (row['log_sha'] - mean_log_sha) / std_log_sha
            })

        # Low |Ш| outliers
        if row["log_sha"] < low_thresh:
            outliers['sha_low'].append({
                'label': label,
                'sha_estimate': row['sha_estimate'],
                'log_sha': row['log_sha'],
                'z_score': (row['log_sha'] - mean_log_sha) / std_log_sha
            })

        # Near-zero regulator (potential numerical instability)
        if abs(row['R']) < 1e-10:
            outliers['regulator_small'].append({
                'label': label,
                'R': row['R'],
                'sha_estimate': row['sha_estimate']
            })

        # Near-zero L-derivative (potential numerical instability)
        if abs(row['l_derivative']) < 1e-10:
            outliers['l_derivative_small'].append({
                'label': label,
                'l_derivative': row['l_derivative'],
                'sha_estimate': row['sha_estimate']
            })

    return outliers


def generate_outlier_report(outliers, output_dir):
    """
    Generate a text report of detected outliers.

    Args:
        outliers: Dictionary with outlier information
        output_dir: Directory to save the report
    """
    report_path = output_dir / "outlier_report.txt"

    with open(report_path, 'w') as f:
        f.write("=" * 60 + "\n")
        f.write("OUTLIER DETECTION REPORT - SHA Estimates Analysis\n")
        f.write("=" * 60 + "\n\n")

        f.write("1. CURVES WITH HIGH |Ш| (> 3σ above mean)\n")
        f.write("-" * 40 + "\n")
        if outliers['sha_high']:
            for item in outliers['sha_high']:
                f.write(f"  {item['label']}: |Ш| ≈ {item['sha_estimate']:.4e}, "
                        f"z-score = {item['z_score']:.2f}\n")
        else:
            f.write("  No outliers detected.\n")

        f.write("\n2. CURVES WITH LOW |Ш| (> 3σ below mean)\n")
        f.write("-" * 40 + "\n")
        if outliers['sha_low']:
            for item in outliers['sha_low']:
                f.write(f"  {item['label']}: |Ш| ≈ {item['sha_estimate']:.4e}, "
                        f"z-score = {item['z_score']:.2f}\n")
        else:
            f.write("  No outliers detected.\n")

        f.write("\n3. CURVES WITH NEAR-ZERO REGULATOR (numerical instability)\n")
        f.write("-" * 40 + "\n")
        if outliers['regulator_small']:
            for item in outliers['regulator_small']:
                f.write(f"  {item['label']}: R = {item['R']:.4e}, "
                        f"|Ш| = {item['sha_estimate']:.4e}\n")
        else:
            f.write("  No issues detected.\n")

        f.write("\n4. CURVES WITH NEAR-ZERO L-DERIVATIVE (numerical instability)\n")
        f.write("-" * 40 + "\n")
        if outliers['l_derivative_small']:
            for item in outliers['l_derivative_small']:
                f.write(f"  {item['label']}: L^(r)(1) = {item['l_derivative']:.4e}, "
                        f"|Ш| = {item['sha_estimate']:.4e}\n")
        else:
            f.write("  No issues detected.\n")

        f.write("\n" + "=" * 60 + "\n")
        total_outliers = (len(outliers['sha_high']) + len(outliers['sha_low']) +
                          len(outliers['regulator_small']) +
                          len(outliers['l_derivative_small']))
        f.write(f"TOTAL OUTLIERS DETECTED: {total_outliers}\n")
        f.write("=" * 60 + "\n")

    print("✅ Saved: outlier_report.txt")


def compute_summary_statistics(df):
    """
    Compute summary statistics for the dataset.

    Args:
        df: DataFrame with SHA estimates

    Returns:
        Dictionary with summary statistics
    """
    stats = {
        'total_curves': len(df),
        'sha_mean': df['sha_estimate'].mean(),
        'sha_median': df['sha_estimate'].median(),
        'sha_std': df['sha_estimate'].std(),
        'sha_min': df['sha_estimate'].min(),
        'sha_max': df['sha_estimate'].max(),
        'log_sha_mean': df['log_sha'].mean(),
        'log_sha_std': df['log_sha'].std(),
        'regulator_mean': df['R'].mean(),
        'l_derivative_mean': df['l_derivative'].mean(),
    }

    if 'rank' in df.columns:
        stats['curves_by_rank'] = df['rank'].value_counts().to_dict()

    return stats


def main():
    """Main entry point for SHA analysis."""
    print("=" * 60)
    print("SHA (Tate-Shafarevich) Group Estimation Analysis")
    print("=" * 60)
    print()

    # Determine paths
    script_dir = Path(__file__).parent
    csv_path = script_dir / "sha_estimates.csv"
    output_dir = script_dir

    # Check if CSV exists
    if not csv_path.exists():
        print(f"❌ CSV file not found: {csv_path}")
        print("   Please ensure sha_estimates.csv exists in the validation folder.")
        sys.exit(1)

    # Load data
    print(f"📂 Loading data from: {csv_path}")
    df = load_sha_estimates(csv_path)
    print(f"   Loaded {len(df)} curves")

    # Compute log transforms
    print("\n📊 Computing log-transforms...")
    df = compute_log_transforms(df)

    # Generate histograms
    print("\n📈 Generating histograms...")
    generate_histogram(df, output_dir, by_rank=True)

    # Generate correlation plots
    print("\n📉 Generating correlation plots...")
    generate_correlation_plots(df, output_dir)

    # Detect outliers
    print("\n🔍 Detecting outliers...")
    outliers = detect_outliers(df)
    generate_outlier_report(outliers, output_dir)

    # Compute summary statistics
    print("\n📋 Computing summary statistics...")
    stats = compute_summary_statistics(df)

    print("\n" + "=" * 60)
    print("SUMMARY STATISTICS")
    print("=" * 60)
    print(f"  Total curves analyzed: {stats['total_curves']}")
    print(f"  |Ш| mean: {stats['sha_mean']:.4e}")
    print(f"  |Ш| median: {stats['sha_median']:.4e}")
    print(f"  |Ш| std dev: {stats['sha_std']:.4e}")
    print(f"  |Ш| range: [{stats['sha_min']:.4e}, {stats['sha_max']:.4e}]")
    print(f"  log(|Ш|) mean: {stats['log_sha_mean']:.4f}")
    print(f"  log(|Ш|) std: {stats['log_sha_std']:.4f}")

    if 'curves_by_rank' in stats:
        print("\n  Curves by rank:")
        for rank, count in sorted(stats['curves_by_rank'].items()):
            print(f"    Rank {rank}: {count} curves")

    print("\n" + "=" * 60)
    print("✅ Analysis complete. Output files saved to:")
    print(f"   {output_dir}")
    print("=" * 60)


if __name__ == "__main__":
    main()
