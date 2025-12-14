"""
BSD Visualization Module - Plots and Charts for BSD Analysis
=============================================================

This module provides visualization functions for BSD curve data,
including Sha distribution plots, anomaly analysis, and rank comparisons.
"""

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from pathlib import Path
from typing import Optional, Tuple


def plot_sha_distribution(
    df: pd.DataFrame,
    ax: Optional[plt.Axes] = None,
    title: str = "Distribución |Ш| - BSD ∞³",
    bins: int = 20
) -> plt.Axes:
    """
    Plot histogram of Sha estimates.

    Args:
        df: DataFrame with BSD curve data
        ax: Matplotlib axes (created if None)
        title: Plot title
        bins: Number of histogram bins

    Returns:
        Matplotlib axes
    """
    if ax is None:
        _, ax = plt.subplots(figsize=(10, 6))

    sha_values = df["sha_estimate"].clip(upper=10)  # Clip outliers for visualization
    ax.hist(sha_values, bins=bins, edgecolor="black", alpha=0.7)
    ax.set_xlabel("|Ш| estimate")
    ax.set_ylabel("Count")
    ax.set_title(title)
    ax.axvline(x=1, color="red", linestyle="--", label="|Ш| = 1")
    ax.legend()

    return ax


def plot_sha2_by_rank(
    df: pd.DataFrame,
    ax: Optional[plt.Axes] = None,
    title: str = "dim(Ш[2]) por rank"
) -> plt.Axes:
    """
    Plot Sha[2] dimension distribution by rank.

    Args:
        df: DataFrame with BSD curve data (must have sha2_dim column)
        ax: Matplotlib axes (created if None)
        title: Plot title

    Returns:
        Matplotlib axes
    """
    if ax is None:
        _, ax = plt.subplots(figsize=(10, 6))

    if "sha2_dim" not in df.columns:
        ax.text(0.5, 0.5, "No sha2_dim data available",
                ha="center", va="center", transform=ax.transAxes)
        ax.set_title(title)
        return ax

    # Group by rank and sha2_dim
    grouped = df.groupby(["rank", "sha2_dim"]).size().unstack(fill_value=0)
    grouped.plot(kind="bar", ax=ax, alpha=0.8)
    ax.set_xlabel("Rank")
    ax.set_ylabel("Count")
    ax.set_title(title)
    ax.legend(title="dim(Ш[2])")
    ax.set_xticklabels(ax.get_xticklabels(), rotation=0)

    return ax


def plot_sha_vs_sha2(
    df: pd.DataFrame,
    ax: Optional[plt.Axes] = None,
    title: str = "BSD: |Ш| vs dim(Ш[2])"
) -> plt.Axes:
    """
    Scatter plot of Sha estimate vs Sha[2] dimension, colored by rank.

    Args:
        df: DataFrame with BSD curve data
        ax: Matplotlib axes (created if None)
        title: Plot title

    Returns:
        Matplotlib axes
    """
    if ax is None:
        _, ax = plt.subplots(figsize=(10, 6))

    if "sha2_dim" not in df.columns:
        ax.text(0.5, 0.5, "No sha2_dim data available",
                ha="center", va="center", transform=ax.transAxes)
        ax.set_title(title)
        return ax

    # Color by rank
    ranks = df["rank"].unique()
    colors = plt.cm.viridis(np.linspace(0, 1, len(ranks)))

    for rank, color in zip(sorted(ranks), colors):
        mask = df["rank"] == rank
        ax.scatter(
            df.loc[mask, "sha_estimate"],
            df.loc[mask, "sha2_dim"],
            c=[color],
            label=f"rank={rank}",
            alpha=0.6
        )

    ax.set_xlabel("|Ш| estimate")
    ax.set_ylabel("dim(Ш[2])")
    ax.set_title(title)
    ax.legend()

    return ax


def plot_anomalies_histogram(
    df: pd.DataFrame,
    ax: Optional[plt.Axes] = None,
    title: str = "Anomalías BSD"
) -> plt.Axes:
    """
    Plot histogram of anomalies by Sha[2] dimension.

    Args:
        df: DataFrame with BSD curve data
        ax: Matplotlib axes (created if None)
        title: Plot title

    Returns:
        Matplotlib axes
    """
    if ax is None:
        _, ax = plt.subplots(figsize=(10, 6))

    if "sha_anomaly" not in df.columns or "sha2_dim" not in df.columns:
        ax.text(0.5, 0.5, "No anomaly data available",
                ha="center", va="center", transform=ax.transAxes)
        ax.set_title(title)
        return ax

    anomalies = df[df["sha_anomaly"]]
    n_anomalies = len(anomalies)

    if n_anomalies > 0:
        ax.hist(anomalies["sha2_dim"], bins=8, edgecolor="black", alpha=0.7, color="orange")
    else:
        ax.text(0.5, 0.5, "No anomalies detected",
                ha="center", va="center", transform=ax.transAxes)

    ax.set_xlabel("dim(Ш[2])")
    ax.set_ylabel("Count")
    ax.set_title(f"{title} (n={n_anomalies})")

    return ax


def plot_sha_by_torsion(
    df: pd.DataFrame,
    ax: Optional[plt.Axes] = None,
    title: str = "Sha estimado por orden torsión"
) -> plt.Axes:
    """
    Box plot of Sha estimates by torsion order.

    Args:
        df: DataFrame with BSD curve data
        ax: Matplotlib axes (created if None)
        title: Plot title

    Returns:
        Matplotlib axes
    """
    if ax is None:
        _, ax = plt.subplots(figsize=(10, 6))

    # Prepare data for box plot
    torsion_orders = sorted(df["torsion_order"].unique())
    data = [df[df["torsion_order"] == t]["sha_estimate"] for t in torsion_orders]

    ax.boxplot(data, labels=torsion_orders)
    ax.set_xlabel("Torsion Order")
    ax.set_ylabel("|Ш| estimate")
    ax.set_title(title)

    return ax


def create_bsd_analysis_plot(
    df: pd.DataFrame,
    save_path: Optional[Path] = None,
    title_prefix: str = "BSD ∞³"
) -> Tuple[plt.Figure, np.ndarray]:
    """
    Create a comprehensive 2x2 analysis plot for BSD data.

    Args:
        df: DataFrame with BSD curve data
        save_path: Optional path to save the figure
        title_prefix: Prefix for plot titles

    Returns:
        Tuple of (figure, axes array)
    """
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1. Sha distribution
    plot_sha_distribution(
        df, ax=axes[0, 0],
        title=f"{title_prefix} — Distribución |Ш|"
    )

    # 2. Sha[2] by rank
    plot_sha2_by_rank(
        df, ax=axes[0, 1],
        title=f"{title_prefix} — dim(Ш[2]) por rank"
    )

    # 3. Sha vs Sha[2] scatter
    plot_sha_vs_sha2(
        df, ax=axes[1, 0],
        title=f"{title_prefix} — |Ш| vs dim(Ш[2])"
    )

    # 4. Sha by torsion
    plot_sha_by_torsion(
        df, ax=axes[1, 1],
        title=f"{title_prefix} — |Ш| por torsión"
    )

    plt.tight_layout()

    if save_path is not None:
        save_path = Path(save_path)
        save_path.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(save_path, dpi=300, bbox_inches="tight")
        print(f"Plot saved to: {save_path}")

    return fig, axes


def create_anomaly_report_plot(
    df: pd.DataFrame,
    save_path: Optional[Path] = None
) -> Tuple[plt.Figure, np.ndarray]:
    """
    Create an anomaly-focused analysis plot.

    Args:
        df: DataFrame with BSD curve data
        save_path: Optional path to save the figure

    Returns:
        Tuple of (figure, axes array)
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # 1. Anomalies histogram
    plot_anomalies_histogram(df, ax=axes[0])

    # 2. Scatter with anomalies highlighted
    ax = axes[1]
    if "sha_anomaly" in df.columns:
        normal = df[~df["sha_anomaly"]]
        anomalies = df[df["sha_anomaly"]]

        ax.scatter(
            normal["sha_estimate"], normal.get("sha2_dim", 0),
            alpha=0.5, label="Normal", color="blue"
        )
        ax.scatter(
            anomalies["sha_estimate"], anomalies.get("sha2_dim", 0),
            alpha=0.8, label="Anomaly", color="red", marker="x", s=100
        )
        ax.set_xlabel("|Ш| estimate")
        ax.set_ylabel("dim(Ш[2])")
        ax.set_title("Anomalies Highlighted")
        ax.legend()
    else:
        ax.text(0.5, 0.5, "No anomaly data", ha="center", va="center",
                transform=ax.transAxes)

    plt.tight_layout()

    if save_path is not None:
        save_path = Path(save_path)
        save_path.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(save_path, dpi=300, bbox_inches="tight")
        print(f"Anomaly plot saved to: {save_path}")

    return fig, axes


if __name__ == "__main__":
    # Demo with simulated data
    from bsd_simulation import generate_complete_bsd_dataset

    print("Generating BSD data for visualization demo...")
    df, stats = generate_complete_bsd_dataset(
        num_curves=500,
        random_seed=42,
        export=False
    )

    # Create analysis plots
    plots_dir = Path(__file__).parent.parent / "plots"
    plots_dir.mkdir(parents=True, exist_ok=True)

    print("\nCreating analysis plots...")
    create_bsd_analysis_plot(
        df,
        save_path=plots_dir / "rank2plus_sha_analysis.png"
    )

    create_anomaly_report_plot(
        df,
        save_path=plots_dir / "bsd_anomaly_report.png"
    )

    print("\n✅ Visualization demo complete!")
