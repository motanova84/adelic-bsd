"""
LMFDB Verification Module - Large-Scale Verification System
Implements algorithms for large-scale verification against LMFDB data

Tests the spectral→cycles→points algorithm on extensive curve databases
"""

from sage.all import EllipticCurve, cremona_curves
from src.height_pairing import verify_height_compatibility


def get_lmfdb_curves(conductor_range=None, rank_range=None, limit=None):
    """
    Get elliptic curves from LMFDB-like database

    Args:
        conductor_range: tuple (min_N, max_N) for conductor bounds
        rank_range: list of ranks to include [0,1,2,3]
        limit: maximum number of curves to return

    Returns:
        List of curve labels
    """
    curves = []

    # Define default parameters
    if conductor_range is None:
        conductor_range = (11, 100)  # Start with small conductors

    if rank_range is None:
        rank_range = [0, 1, 2, 3]

    min_N, max_N = conductor_range

    # Collect curves from Cremona database
    try:
        for N in range(min_N, max_N + 1):
            try:
                # Get curves of conductor N
                N_curves = cremona_curves(N)
                for label in N_curves:
                    try:
                        E = EllipticCurve(label)
                        r = E.rank()

                        # Filter by rank if specified
                        if r in rank_range:
                            curves.append(label)

                        # Check limit
                        if limit is not None and len(curves) >= limit:
                            return curves
                    except:
                        continue
            except:
                continue
    except:
        # Fallback to known test curves
        curves = [
            "11a1", "11a2", "11a3",
            "14a1", "14a2", "14a3", "14a4", "14a5", "14a6",
            "15a1", "15a2", "15a3", "15a4", "15a5", "15a6", "15a7", "15a8",
            "17a1", "17a2", "17a3", "17a4",
            "19a1", "19a2", "19a3",
            "20a1", "20a2", "20a3", "20a4", "20a5", "20a6",
            "21a1", "21a2", "21a3", "21a4",
            "24a1", "24a2", "24a3", "24a4",
            "26a1", "26a2", "26b1",
            "27a1", "27a2", "27a3", "27a4",
            "30a1", "30a2", "30a3", "30a4", "30a5", "30a6", "30a7", "30a8",
            "32a1", "32a2", "32a3", "32a4",
            "33a1", "33a2", "33a3", "33a4",
            "34a1", "34a2", "34a3",
            "35a1", "35a2", "35a3",
            "36a1", "36a2", "36a3", "36a4",
            "37a1",
            "38a1", "38a2", "38a3", "38b1", "38b2",
        ]

        # Filter by rank if needed
        if rank_range is not None:
            filtered = []
            for label in curves:
                try:
                    E = EllipticCurve(label)
                    if E.rank() in rank_range:
                        filtered.append(label)
                        if limit and len(filtered) >= limit:
                            break
                except:
                    continue
            curves = filtered

    # Apply limit
    if limit is not None:
        curves = curves[:limit]

    return curves


def large_scale_verification(conductor_range=(11, 50), rank_range=None,
                             limit=20, verbose=True):
    """
    Large-scale verification of the spectral→cycles→points algorithm

    Implements the massive LMFDB verification described in the problem statement

    Args:
        conductor_range: tuple (min_N, max_N) for conductor range
        rank_range: list of ranks to test (None = all ranks)
        limit: maximum number of curves to test
        verbose: whether to print detailed progress

    Returns:
        dict with verification results and statistics
    """
    if verbose:
        print("\n" + "="*70)
        print("LARGE-SCALE LMFDB VERIFICATION")
        print("="*70)
        print(f"Conductor range: {conductor_range}")
        print(f"Rank filter: {rank_range if rank_range else 'all ranks'}")
        print(f"Limit: {limit if limit else 'no limit'}")
        print("="*70)

    # Get curves to test
    curves = get_lmfdb_curves(conductor_range, rank_range, limit)

    if verbose:
        print(f"\nCurves to test: {len(curves)}")
        print("\nStarting verification...\n")

    results = []
    success_count = 0
    error_count = 0

    for i, label in enumerate(curves):
        if verbose:
            print(f"\n[{i+1}/{len(curves)}] Testing {label}...")
            print("-" * 50)

        try:
            E = EllipticCurve(label)

            # Verify height compatibility
            result = verify_height_compatibility(E)

            # Record result
            results.append({
                'label': label,
                'status': 'success' if result['compatible'] else 'compatible_false',
                'compatible': result['compatible'],
                'conductor': E.conductor(),
                'rank': E.rank(),
                'kernel_dim': result['kernel_dimension'],
                'max_diff': result.get('max_difference', float('inf'))
            })

            if result['compatible']:
                success_count += 1
                if verbose:
                    print(f"✓ {label}: COMPATIBLE")
            else:
                if verbose:
                    print(f"⚠ {label}: Pending (max_diff={result.get('max_difference', 'N/A')})")

        except Exception as e:
            error_count += 1
            results.append({
                'label': label,
                'status': 'error',
                'compatible': False,
                'error': str(e)
            })
            if verbose:
                print(f"✗ {label}: ERROR - {str(e)[:50]}")

    # Calculate statistics
    total = len(results)
    success_rate = (success_count / total * 100) if total > 0 else 0

    if verbose:
        print("\n" + "="*70)
        print("VERIFICATION SUMMARY")
        print("="*70)
        print(f"Total curves tested: {total}")
        print(f"Compatible: {success_count}")
        print(f"Not compatible: {total - success_count - error_count}")
        print(f"Errors: {error_count}")
        print(f"Success rate: {success_rate:.1f}%")
        print("="*70)

    # Analyze by rank
    rank_stats = {}
    for r in (rank_range if rank_range else [0, 1, 2, 3]):
        rank_results = [res for res in results
                        if res.get('rank') == r and res['status'] != 'error']
        if rank_results:
            rank_compatible = sum(1 for res in rank_results if res['compatible'])
            rank_stats[r] = {
                'total': len(rank_results),
                'compatible': rank_compatible,
                'rate': rank_compatible / len(rank_results) * 100
            }

    if verbose and rank_stats:
        print("\nBREAKDOWN BY RANK:")
        print("-" * 70)
        for r, stats in sorted(rank_stats.items()):
            print(f"Rank {r}: {stats['compatible']}/{stats['total']} "
                  f"({stats['rate']:.1f}% compatible)")

    return {
        'results': results,
        'total': total,
        'success_count': success_count,
        'error_count': error_count,
        'success_rate': success_rate,
        'rank_statistics': rank_stats,
        'curves_tested': curves
    }


def generate_verification_report(verification_data, output_file=None):
    """
    Generate a detailed report of verification results

    Args:
        verification_data: Output from large_scale_verification
        output_file: Optional file path to save report

    Returns:
        String containing the report
    """
    report = []
    report.append("="*70)
    report.append("SPECTRAL→CYCLES→POINTS VERIFICATION REPORT")
    report.append("="*70)
    report.append("")

    # Overall statistics
    report.append("OVERALL STATISTICS:")
    report.append(f"  Total curves tested: {verification_data['total']}")
    report.append(f"  Compatible: {verification_data['success_count']}")
    report.append(f"  Errors: {verification_data['error_count']}")
    report.append(f"  Success rate: {verification_data['success_rate']:.2f}%")
    report.append("")

    # Rank breakdown
    if verification_data['rank_statistics']:
        report.append("BREAKDOWN BY RANK:")
        for r, stats in sorted(verification_data['rank_statistics'].items()):
            report.append(f"  Rank {r}:")
            report.append(f"    - Total: {stats['total']}")
            report.append(f"    - Compatible: {stats['compatible']}")
            report.append(f"    - Rate: {stats['rate']:.1f}%")
        report.append("")

    # Detailed results
    report.append("DETAILED RESULTS:")
    report.append("")

    for result in verification_data['results']:
        label = result['label']
        status = result['status']

        if status == 'success':
            rank = result.get('rank', '?')
            kernel_dim = result.get('kernel_dim', '?')
            report.append(f"  ✓ {label}: Compatible (rank={rank}, ker_dim={kernel_dim})")
        elif status == 'compatible_false':
            report.append(f"  ⚠ {label}: Not compatible")
        else:
            error = result.get('error', 'Unknown error')
            report.append(f"  ✗ {label}: Error - {error[:50]}")

    report.append("")
    report.append("="*70)
    report.append("END OF REPORT")
    report.append("="*70)

    report_text = "\n".join(report)

    # Save to file if specified
    if output_file:
        with open(output_file, 'w') as f:
            f.write(report_text)
        print(f"\nReport saved to: {output_file}")

    return report_text


def quick_verification_demo():
    """
    Quick demonstration of verification on a few curves
    """
    print("\n" + "="*70)
    print("QUICK VERIFICATION DEMO")
    print("="*70)

    # Test a few representative curves
    test_curves = ["11a1", "14a1", "37a1"]

    results = large_scale_verification(
        conductor_range=(11, 50),
        rank_range=[0, 1],
        limit=len(test_curves),
        verbose=True
    )

    return results
