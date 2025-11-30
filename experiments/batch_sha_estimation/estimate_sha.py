"""
BSD Estimator of |Ш| for Elliptic Curves

Calculates the Tate-Shafarevich group cardinality |Ш(E)| for elliptic curves
with rank ≥ 2, using the BSD (Birch and Swinnerton-Dyer) formula.

BSD Formula:
|Ш(E)| = L^{(r)}(E,1) / (r! * Ω_E * R_E * |Tors(E)|² * ∏c_p)

Where:
- L^{(r)}(E,1) = r-th derivative of L(E,s) at s=1 (r = rank of E)
- Ω_E = real period (or imaginary for CM curves)
- R_E = regulator (determinant of height pairing matrix)
- Tors(E) = torsion subgroup
- ∏c_p = product of Tamagawa numbers at all primes of bad reduction

Author: adelic-bsd development team
Compatible with Python 3.9-3.13
"""

import csv
import os
from dataclasses import dataclass, asdict
from math import factorial
from typing import List, Optional


@dataclass
class ShaEstimationResult:
    """Result of a BSD-based Sha estimation for an elliptic curve."""

    label: str
    rank: int
    sha_estimate: Optional[float]
    l_derivative: Optional[float]
    omega: Optional[float]
    regulator: Optional[float]
    torsion_order: int
    tamagawa_product: int
    success: bool
    error_message: Optional[str] = None

    def to_dict(self) -> dict:
        """Convert to dictionary for JSON/CSV export."""
        return asdict(self)


def estimate_sha(label: str) -> ShaEstimationResult:
    """
    Estimate |Ш(E)| for an elliptic curve given its LMFDB or Cremona label.

    The estimation uses the BSD conjecture formula. This function only
    processes curves with rank ≥ 2.

    Args:
        label: LMFDB label (e.g., "389.a1" or "389a1") or Cremona label

    Returns:
        ShaEstimationResult containing the estimation details

    Raises:
        ImportError: If SageMath is not available
    """
    try:
        from sage.all import EllipticCurve
    except ImportError as e:
        return ShaEstimationResult(
            label=label,
            rank=-1,
            sha_estimate=None,
            l_derivative=None,
            omega=None,
            regulator=None,
            torsion_order=0,
            tamagawa_product=0,
            success=False,
            error_message=f"SageMath not available: {e}",
        )

    try:
        # Try LMFDB label first, then Cremona label
        try:
            E = EllipticCurve(lmfdb_label=label)
        except (ValueError, RuntimeError):
            # Try as Cremona label
            E = EllipticCurve(label)

        return estimate_sha_from_curve(E, label)

    except Exception as e:
        return ShaEstimationResult(
            label=label,
            rank=-1,
            sha_estimate=None,
            l_derivative=None,
            omega=None,
            regulator=None,
            torsion_order=0,
            tamagawa_product=0,
            success=False,
            error_message=str(e),
        )


def estimate_sha_from_curve(E, label: Optional[str] = None) -> ShaEstimationResult:
    """
    Estimate |Ш(E)| from an EllipticCurve object.

    Args:
        E: SageMath EllipticCurve object
        label: Optional label for the curve (auto-detected if not provided)

    Returns:
        ShaEstimationResult containing the estimation details
    """
    try:
        from sage.all import prod
    except ImportError as e:
        lbl = label or str(E)
        return ShaEstimationResult(
            label=lbl,
            rank=-1,
            sha_estimate=None,
            l_derivative=None,
            omega=None,
            regulator=None,
            torsion_order=0,
            tamagawa_product=0,
            success=False,
            error_message=f"SageMath not available: {e}",
        )

    try:
        # Determine label
        if label is None:
            try:
                label = E.cremona_label()
            except (AttributeError, RuntimeError):
                label = str(E.ainvs())

        # Get rank
        r = E.rank()

        # Only process curves with rank >= 2
        if r < 2:
            return ShaEstimationResult(
                label=label,
                rank=r,
                sha_estimate=None,
                l_derivative=None,
                omega=None,
                regulator=None,
                torsion_order=int(E.torsion_order()),
                tamagawa_product=int(prod(E.tamagawa_numbers())),
                success=False,
                error_message=f"Rank {r} < 2, skipping (only rank >= 2 supported)",
            )

        # Compute L-series derivative at s=1
        # L^{(r)}(E, 1) = r-th derivative evaluated at s=1
        L = E.lseries()

        # Use numerical evaluation
        try:
            # This computes the r-th derivative at s=1
            Lr = float(L.derivative(r)(1))
        except (AttributeError, ValueError, TypeError, RuntimeError):
            # Fallback: try computing via leading coefficient
            try:
                Lr = float(L.dokchitser().taylor_series(1, r + 1).coefficient(r)) * factorial(r)
            except (AttributeError, ValueError, TypeError, RuntimeError) as e:
                return ShaEstimationResult(
                    label=label,
                    rank=r,
                    sha_estimate=None,
                    l_derivative=None,
                    omega=None,
                    regulator=None,
                    torsion_order=int(E.torsion_order()),
                    tamagawa_product=int(prod(E.tamagawa_numbers())),
                    success=False,
                    error_message=f"Failed to compute L-derivative: {e}",
                )

        # Torsion order
        tors_order = int(E.torsion_order())

        # Regulator
        try:
            R = float(E.regulator())
        except Exception as e:
            return ShaEstimationResult(
                label=label,
                rank=r,
                sha_estimate=None,
                l_derivative=Lr,
                omega=None,
                regulator=None,
                torsion_order=tors_order,
                tamagawa_product=int(prod(E.tamagawa_numbers())),
                success=False,
                error_message=f"Failed to compute regulator: {e}",
            )

        # Real period (Omega)
        try:
            Omega = float(E.period_lattice().real_volume())
        except Exception:
            # Fallback for curves without real period
            try:
                Omega = float(E.real_components()) * float(E.period_lattice().omega(prec=53))
            except Exception as e:
                return ShaEstimationResult(
                    label=label,
                    rank=r,
                    sha_estimate=None,
                    l_derivative=Lr,
                    omega=None,
                    regulator=R,
                    torsion_order=tors_order,
                    tamagawa_product=int(prod(E.tamagawa_numbers())),
                    success=False,
                    error_message=f"Failed to compute period: {e}",
                )

        # Tamagawa numbers product
        tamagawa = int(prod(E.tamagawa_numbers()))

        # BSD formula:
        # |Sha| = L^{(r)}(E,1) / (r! * Omega * R * |Tors|^2 * prod(c_p))
        denominator = factorial(r) * Omega * R * (tors_order ** 2) * tamagawa

        if abs(denominator) < 1e-15:
            return ShaEstimationResult(
                label=label,
                rank=r,
                sha_estimate=None,
                l_derivative=Lr,
                omega=Omega,
                regulator=R,
                torsion_order=tors_order,
                tamagawa_product=tamagawa,
                success=False,
                error_message="Denominator is effectively zero",
            )

        sha = Lr / denominator

        return ShaEstimationResult(
            label=label,
            rank=r,
            sha_estimate=round(sha, 10),
            l_derivative=round(Lr, 10),
            omega=round(Omega, 10),
            regulator=round(R, 10),
            torsion_order=tors_order,
            tamagawa_product=tamagawa,
            success=True,
            error_message=None,
        )

    except Exception as e:
        lbl = label or "unknown"
        return ShaEstimationResult(
            label=lbl,
            rank=-1,
            sha_estimate=None,
            l_derivative=None,
            omega=None,
            regulator=None,
            torsion_order=0,
            tamagawa_product=0,
            success=False,
            error_message=str(e),
        )


def get_curves_by_rank(
    min_rank: int = 2,
    max_rank: int = 3,
    limit_per_rank: Optional[int] = None,
    conductor_max: int = 10000,
) -> List[str]:
    """
    Get elliptic curve labels filtered by rank.

    Args:
        min_rank: Minimum rank to include
        max_rank: Maximum rank to include
        limit_per_rank: Maximum curves per rank (None for unlimited)
        conductor_max: Maximum conductor to search

    Returns:
        List of curve labels
    """
    try:
        from sage.all import EllipticCurve, cremona_curves
    except ImportError:
        # Return well-known high-rank curves when SageMath is unavailable
        known_curves = {
            2: [
                "389a1", "433a1", "446a1", "563a1", "571a1", "643a1",
                "655a1", "664a1", "681a1", "707a1", "709a1", "718a1",
            ],
            3: [
                "5077a1", "234446a1", "1025058a1",
            ],
        }
        result = []
        for r in range(min_rank, max_rank + 1):
            curves = known_curves.get(r, [])
            if limit_per_rank:
                curves = curves[:limit_per_rank]
            result.extend(curves)
        return result

    curves_by_rank = {r: [] for r in range(min_rank, max_rank + 1)}

    # Default search limit for performance - use conductor_max if lower
    # This prevents excessive search times for large conductor_max values
    SEARCH_LIMIT = 500  # Balance between coverage and performance

    try:
        # Iterate through curves in the Cremona database
        for N in range(11, min(conductor_max + 1, SEARCH_LIMIT)):
            try:
                for label in cremona_curves(N):
                    try:
                        E = EllipticCurve(label)
                        r = E.rank()
                        if min_rank <= r <= max_rank:
                            curves_by_rank[r].append(label)

                            # Check limit
                            if limit_per_rank:
                                all_done = all(
                                    len(curves_by_rank[rank]) >= limit_per_rank
                                    for rank in curves_by_rank
                                )
                                if all_done:
                                    break
                    except Exception:
                        continue
            except Exception:
                continue

            # Early exit if limits reached
            if limit_per_rank:
                all_done = all(
                    len(curves_by_rank[rank]) >= limit_per_rank
                    for rank in curves_by_rank
                )
                if all_done:
                    break
    except Exception:
        pass

    # Flatten results
    result = []
    for r in range(min_rank, max_rank + 1):
        curves = curves_by_rank[r]
        if limit_per_rank:
            curves = curves[:limit_per_rank]
        result.extend(curves)

    return result


def batch_estimate_sha(
    labels: Optional[List[str]] = None,
    min_rank: int = 2,
    max_rank: int = 3,
    limit_rank2: int = 500,
    limit_rank3: int = 50,
    verbose: bool = True,
) -> List[ShaEstimationResult]:
    """
    Estimate |Ш| for a batch of elliptic curves.

    Args:
        labels: List of curve labels (if None, auto-discover curves)
        min_rank: Minimum rank filter
        max_rank: Maximum rank filter
        limit_rank2: Maximum number of rank-2 curves to process
        limit_rank3: Maximum number of rank-3 curves to process
        verbose: Whether to print progress

    Returns:
        List of ShaEstimationResult objects
    """
    if verbose:
        print("=" * 70)
        print("BATCH SHA ESTIMATION FOR HIGH-RANK ELLIPTIC CURVES")
        print("=" * 70)

    # Get curves if not provided
    if labels is None:
        if verbose:
            print(f"Discovering curves with rank {min_rank}-{max_rank}...")

        # Get curves for each rank with respective limits
        rank2_curves = get_curves_by_rank(2, 2, limit_rank2)
        rank3_curves = get_curves_by_rank(3, 3, limit_rank3)
        labels = rank2_curves + rank3_curves

        if verbose:
            print(f"Found {len(rank2_curves)} rank-2 curves, {len(rank3_curves)} rank-3 curves")

    total = len(labels)
    if verbose:
        print(f"Processing {total} curves...")
        print("-" * 70)

    results = []
    success_count = 0

    for i, label in enumerate(labels):
        if verbose and (i + 1) % 10 == 0:
            print(f"Progress: {i + 1}/{total} curves processed...")

        result = estimate_sha(label)
        results.append(result)

        if result.success:
            success_count += 1
            if verbose:
                print(
                    f"  ✓ {label}: rank={result.rank}, |Ш| ≈ {result.sha_estimate}"
                )
        else:
            if verbose and "rank" not in (result.error_message or "").lower():
                print(f"  ✗ {label}: {result.error_message}")

    if verbose:
        print("-" * 70)
        print(f"Completed: {success_count}/{total} successful estimations")
        print("=" * 70)

    return results


def export_results_to_csv(
    results: List[ShaEstimationResult],
    output_path: str = "sha_estimation_results.csv",
) -> str:
    """
    Export estimation results to a CSV file.

    CSV columns:
    - label: Curve label
    - rank: Algebraic rank
    - sha_estimate: Estimated |Ш|
    - l_derivative: L^{(r)}(E, 1)
    - omega: Real period Ω_E
    - R: Regulator R_E
    - torsion: |Tors(E)|
    - tamagawa: ∏c_p

    Args:
        results: List of ShaEstimationResult objects
        output_path: Path for the output CSV file

    Returns:
        Absolute path to the saved CSV file
    """
    # Prepare data
    fieldnames = [
        "label",
        "rank",
        "sha_estimate",
        "l_derivative",
        "omega",
        "R",
        "torsion",
        "tamagawa",
        "success",
        "error_message",
    ]

    rows = []
    for result in results:
        rows.append({
            "label": result.label,
            "rank": result.rank,
            "sha_estimate": result.sha_estimate,
            "l_derivative": result.l_derivative,
            "omega": result.omega,
            "R": result.regulator,
            "torsion": result.torsion_order,
            "tamagawa": result.tamagawa_product,
            "success": result.success,
            "error_message": result.error_message or "",
        })

    # Write CSV
    with open(output_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    return os.path.abspath(output_path)


def main():
    """Main entry point for command-line usage."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Estimate |Ш(E)| for elliptic curves using BSD formula"
    )
    parser.add_argument(
        "--labels",
        nargs="+",
        help="Specific curve labels to process",
    )
    parser.add_argument(
        "--limit-rank2",
        type=int,
        default=500,
        help="Max number of rank-2 curves (default: 500)",
    )
    parser.add_argument(
        "--limit-rank3",
        type=int,
        default=50,
        help="Max number of rank-3 curves (default: 50)",
    )
    parser.add_argument(
        "--output",
        default="sha_estimation_results.csv",
        help="Output CSV file path",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress verbose output",
    )

    args = parser.parse_args()

    # Run batch estimation
    results = batch_estimate_sha(
        labels=args.labels,
        limit_rank2=args.limit_rank2,
        limit_rank3=args.limit_rank3,
        verbose=not args.quiet,
    )

    # Export results
    output_path = export_results_to_csv(results, args.output)
    print(f"\nResults saved to: {output_path}")

    # Summary statistics
    successful = [r for r in results if r.success]
    if successful:
        print("\nSummary of successful estimations:")
        print(f"  Total: {len(successful)}")
        sha_values = [r.sha_estimate for r in successful if r.sha_estimate is not None]
        if sha_values:
            avg_sha = sum(sha_values) / len(sha_values)
            print(f"  Average |Ш|: {avg_sha:.4f}")


if __name__ == "__main__":
    main()
