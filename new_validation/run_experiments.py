#!/usr/bin/env python3
"""
BSD Genesis Experimental Validation Runner
============================================

Main script to run BSD experimental validation on curves not covered
by classical proofs (rank ≥ 2, conductor > 1000).

Usage:
    python -m new_validation.run_experiments

Or with SageMath:
    sage -python run_experiments.py

Author: BSD Spectral Framework
Date: November 2025
"""

import json
import os
import sys


def run_all_experiments(output_base_dir=None):
    """
    Run BSD experimental validation on all experimental curves.

    Args:
        output_base_dir: Base directory for output files

    Returns:
        dict: Summary of all experiments
    """
    # Set default output directory
    if output_base_dir is None:
        # Try to find the repository root
        script_dir = os.path.dirname(os.path.abspath(__file__))
        output_base_dir = os.path.join(script_dir)

    print("=" * 70)
    print("BSD GENESIS - EXPERIMENTAL VALIDATION")
    print("=" * 70)
    print()

    # Try to import SageMath
    try:
        from sage.all import EllipticCurve
        sage_available = True
        print("✓ SageMath detected")
    except ImportError:
        sage_available = False
        print("⚠ SageMath not available - running in demo mode")
        print("  Install SageMath for full curve computations")
        print()

    # Import our modules
    from .curve_generator import get_experimental_curve_definitions
    from .bsd_experiment import run_bsd_experiment
    from .qcal_seal import generate_qcal_seal, generate_seal_certificate
    from .summary_generator import generate_all_summaries

    # Get curve definitions
    curve_defs = get_experimental_curve_definitions()
    print(f"\nCurves to validate: {len(curve_defs)}")

    for label, info in curve_defs.items():
        print(f"  - {label}: {info['description']}")
    print()

    # Run experiments
    all_results = []

    if sage_available:
        for label, info in curve_defs.items():
            print("\n" + "=" * 60)
            print(f"Processing: {label}")
            print("=" * 60)

            try:
                # Create output directory for this curve
                curve_output_dir = os.path.join(output_base_dir, label)

                # Load curve
                if 'cremona_label' in info:
                    try:
                        E = EllipticCurve(info['cremona_label'])
                    except Exception:
                        E = EllipticCurve(info['coefficients'])
                else:
                    E = EllipticCurve(info['coefficients'])

                print(f"  Curve loaded: {E}")
                print(f"  Conductor: {E.conductor()}")
                print(f"  Rank: {E.rank()}")

                # Run BSD experiment
                result = run_bsd_experiment(E, label, curve_output_dir)

                # Generate QCAL seal
                seal = generate_qcal_seal(result['comparison'])
                seal_path = os.path.join(curve_output_dir, 'qcal_seal.json')
                with open(seal_path, 'w') as f:
                    json.dump(seal, f, indent=2)

                # Save seal certificate
                cert = generate_seal_certificate(seal)
                cert_path = os.path.join(curve_output_dir, 'seal_certificate.txt')
                with open(cert_path, 'w') as f:
                    f.write(cert)

                # Print summary
                comparison = result['comparison']
                if comparison.get('sha_estimate') is not None:
                    print("\n  BSD Comparison:")
                    print(f"    LHS: {comparison.get('lhs', 'N/A'):.10e}")
                    print(f"    RHS: {comparison.get('rhs_sha_1', 'N/A'):.10e}")
                    print(f"    Sha estimate: {comparison.get('sha_estimate', 'N/A'):.6f}")
                    print(f"    Error: {comparison.get('relative_error', 0) * 100:.4f}%")

                    if comparison.get('sha_is_1'):
                        print("    Status: ✓ Experimental match (Sha ≈ 1)")
                    else:
                        print("    Status: × Mismatch or further analysis needed")
                else:
                    print("\n  Could not compute full BSD comparison")

                all_results.append(result)
                print(f"\n  Output saved to: {curve_output_dir}")

            except Exception as e:
                print(f"  ERROR: {str(e)}")
                import traceback
                traceback.print_exc()

                all_results.append({
                    'label': label,
                    'error': str(e),
                    'comparison': {},
                })

    else:
        # Demo mode without SageMath
        print("\nRunning in demo mode (no SageMath)...")
        print("Creating placeholder results...")

        for label, info in curve_defs.items():
            all_results.append({
                'label': label,
                'comparison': {
                    'terms': {
                        'conductor': info.get('expected_conductor', 5077),
                        'rank': info.get('expected_rank', 0),
                        'j_invariant': 'demo_mode',
                        'torsion': {'order': 1, 'structure': []},
                        'omega': {'omega_plus': 1.0},
                        'regulator': {'value': 1.0},
                        'tamagawa': {'product': 1},
                    },
                    'lhs': None,
                    'rhs_sha_1': None,
                    'sha_estimate': None,
                },
                'demo_mode': True,
            })

    # Generate summaries
    print("\n" + "=" * 60)
    print("Generating Summary Files")
    print("=" * 60)

    summary_files = generate_all_summaries(all_results, output_base_dir)
    print(f"  CSV: {summary_files['csv']}")
    print(f"  README: {summary_files['readme']}")
    print(f"  JSON: {summary_files['json']}")

    # Print final summary
    print("\n" + "=" * 70)
    print("VALIDATION COMPLETE")
    print("=" * 70)

    successful = sum(1 for r in all_results
                     if r.get('comparison', {}).get('sha_is_1', False))
    total = len(all_results)

    print(f"Total curves: {total}")
    print(f"Successful matches (Sha ≈ 1): {successful}")
    if total > 0:
        print(f"Match rate: {successful / total * 100:.1f}%")
    else:
        print("Match rate: N/A")

    return {
        'results': all_results,
        'summary_files': summary_files,
        'total': total,
        'successful': successful,
    }


if __name__ == '__main__':
    # Get script directory for output
    script_dir = os.path.dirname(os.path.abspath(__file__))

    # Run experiments
    summary = run_all_experiments(script_dir)

    # Exit with appropriate code
    sys.exit(0 if summary['successful'] > 0 else 1)
