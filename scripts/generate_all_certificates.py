#!/usr/bin/env python3
"""
Generate finiteness certificates for a range of elliptic curves
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve, cremona_curves
from src.spectral_finiteness import SpectralFinitenessProver
from src.utils import get_safe_output_path


def generate_certificates_for_conductor_range(max_conductor=100, output_dir='certificates'):
    """
    Generate certificates for all curves up to a given conductor

    Args:
        max_conductor: Maximum conductor to process
        output_dir: Directory to save certificates
    """
    # Use safe directory for file writing
    full_output_dir = get_safe_output_path(output_dir, is_dir=True)

    print(f"🚀 Generating certificates for curves with conductor <= {max_conductor}")
    print(f"📁 Output directory: {full_output_dir}/")
    print("=" * 70)

    total = 0
    successful = 0
    failed = 0

    try:
        # Get all curves up to max_conductor
        for label in cremona_curves(max_conductor):
            total += 1

            try:
                E = EllipticCurve(label)
                prover = SpectralFinitenessProver(E)

                # Prove finiteness
                result = prover.prove_finiteness()

                # Generate certificate
                cert = prover.generate_certificate('text')

                # Save to file
                filename = os.path.join(full_output_dir, f"certificate_{label}.txt")
                with open(filename, 'w') as f:
                    f.write(cert)

                print(f"✓ {label}: Certificate generated (bound={result['global_bound']})")
                successful += 1

            except Exception as e:
                print(f"✗ {label}: ERROR - {e}")
                failed += 1

    except Exception as e:
        print(f"\n⚠ Warning: Could not enumerate all curves: {e}")
        print("   Continuing with available curves...")

    # Summary
    print("=" * 70)
    print("📊 SUMMARY:")
    print(f"   Total curves processed: {total}")
    print(f"   Successful: {successful}")
    print(f"   Failed: {failed}")
    print(f"   Success rate: {100*successful/total if total > 0 else 0:.1f}%")
    print(f"\n📁 Certificates saved in: {full_output_dir}/")

    return successful, failed


def generate_certificates_for_specific_curves(curve_labels, output_dir='certificates'):
    """
    Generate certificates for a specific list of curves

    Args:
        curve_labels: List of curve labels (e.g., ['11a1', '37a1'])
        output_dir: Directory to save certificates
    """
    # Use safe directory for file writing
    full_output_dir = get_safe_output_path(output_dir, is_dir=True)

    print(f"🚀 Generating certificates for {len(curve_labels)} specific curves")
    print(f"📁 Output directory: {full_output_dir}/")
    print("=" * 70)

    successful = 0
    failed = 0

    for label in curve_labels:
        try:
            E = EllipticCurve(label)
            prover = SpectralFinitenessProver(E)

            # Prove finiteness
            result = prover.prove_finiteness()

            # Generate certificate
            cert = prover.generate_certificate('text')

            # Save to file
            filename = os.path.join(full_output_dir, f"certificate_{label}.txt")
            with open(filename, 'w') as f:
                f.write(cert)

            print(f"✓ {label}: Certificate generated (bound={result['global_bound']})")
            successful += 1

        except Exception as e:
            print(f"✗ {label}: ERROR - {e}")
            failed += 1

    # Summary
    print("=" * 70)
    print("📊 SUMMARY:")
    print(f"   Successful: {successful}/{len(curve_labels)}")
    print(f"   Failed: {failed}/{len(curve_labels)}")
    print(f"\n📁 Certificates saved in: {full_output_dir}/")

    return successful, failed


def main():
    """Main entry point"""
    import argparse

    parser = argparse.ArgumentParser(
        description='Generate spectral finiteness certificates for elliptic curves'
    )
    parser.add_argument(
        '--conductor',
        type=int,
        default=50,
        help='Maximum conductor to process (default: 50)'
    )
    parser.add_argument(
        '--curves',
        nargs='+',
        help='Specific curve labels to process (e.g., 11a1 37a1)'
    )
    parser.add_argument(
        '--output',
        default='certificates',
        help='Output directory for certificates (default: certificates)'
    )

    args = parser.parse_args()

    if args.curves:
        # Process specific curves
        generate_certificates_for_specific_curves(args.curves, args.output)
    else:
        # Process by conductor range
        generate_certificates_for_conductor_range(args.conductor, args.output)

    print("\n✅ Certificate generation complete!")


if __name__ == "__main__":
    main()
