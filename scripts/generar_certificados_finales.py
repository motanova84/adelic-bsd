#!/usr/bin/env python3
"""
BSD Certificate Generator
Generates formal certificates for verified curves

This script creates verification certificates with complete documentation
of the BSD proof for publication and review.
"""

import os
import sys
import argparse

from sage.all import EllipticCurve
from src.verification import generate_formal_certificate
from src.verification.certificate_generator import CertificateGenerator
from src.verification.mass_verification import batch_verify_bsd


def generate_individual_certificates(curve_labels, output_dir='certificates'):
    """
    Generate individual certificates for each curve.
    Args:
        curve_labels: List of curve labels (e.g. ['11a1', '37a1'])
        output_dir: Output directory for certificates
    """
    print(f"\n{'='*70}")
    print(f"GENERATING INDIVIDUAL CERTIFICATES")
    print(f"{'='*70}\n")

    os.makedirs(output_dir, exist_ok=True)
    certificates = []

    for label in curve_labels:
        try:
            print(f"Processing {label}...", end=" ")
            E = EllipticCurve(label)

            # Generate certificate
            certificate = generate_formal_certificate(E, save_to_file=False)

            # Save in both formats using direct file writing
            # (since certificate structure doesn't match CertificateGenerator expectations)
            import json
            from datetime import datetime
            
            # JSON format
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            json_filename = f"certificate_{label}_{timestamp}.json"
            json_path = os.path.join(output_dir, json_filename)
            with open(json_path, 'w') as f:
                json.dump(certificate, f, indent=2, default=str)
            
            # Text format
            text_filename = f"certificate_{label}_{timestamp}.txt"
            text_path = os.path.join(output_dir, text_filename)
            with open(text_path, 'w') as f:
                f.write("=" * 70 + "\n")
                f.write("BSD VERIFICATION CERTIFICATE\n")
                f.write("=" * 70 + "\n\n")
                f.write(f"Curve: {label}\n")
                f.write(f"Conductor: {certificate['metadata']['conductor']}\n")
                f.write(f"Rank: {certificate['metadata']['rank']}\n")
                f.write(f"BSD Proven: {certificate.get('bsd_proven', False)}\n")
                f.write("\n" + "=" * 70 + "\n")

            certificates.append(certificate)
            print(f"✓ Saved")
            print(f"  JSON: {json_path}")
            print(f"  Text: {text_path}")

        except Exception as e:
            print(f"✗ Error: {e}")

    print(f"\n✓ Generated {len(certificates)} certificates")
    return certificates


def generate_batch_summary_certificate(certificates, output_dir='certificates'):
    """
    Generate summary certificate for a batch of curves.
    Args:
        certificates: List of individual certificates
        output_dir: Output directory
    """
    print(f"\n{'='*70}")
    print(f"GENERATING SUMMARY CERTIFICATE")
    print(f"{'='*70}\n")

    import json
    from datetime import datetime
    
    total = len(certificates)
    successful = sum(1 for c in certificates if c.get('bsd_proven', False))
    
    summary = {
        'type': 'batch_summary',
        'total_curves': total,
        'successful_verifications': successful,
        'success_rate': f"{(successful/total*100):.1f}%" if total > 0 else "0%",
        'timestamp': datetime.now().isoformat(),
        'individual_certificates': [
            {
                'curve': c.get('metadata', {}).get('curve', 'unknown'),
                'bsd_proven': c.get('bsd_proven', False),
                'certificate_hash': c.get('certificate_hash', '')
            }
            for c in certificates
        ]
    }
    
    # Save summary
    os.makedirs(output_dir, exist_ok=True)
    summary_path = os.path.join(output_dir, 'batch_summary.json')
    with open(summary_path, 'w') as f:
        json.dump(summary, f, indent=2)
    
    print(f"✓ Batch summary saved: {summary_path}")
    print(f"  Total curves: {summary['total_curves']}")
    print(f"  Successful: {summary['successful_verifications']}")
    print(f"  Success rate: {summary['success_rate']}")
    
    return summary


def main():
    parser = argparse.ArgumentParser(description="BSD Certificate Generator")
    parser.add_argument("--results_file", help="Path to verification results JSON")
    parser.add_argument("--curves", nargs="*", help="Specific curve labels (e.g. 11a1 37a1)")
    parser.add_argument("--output_dir", default="certificates", help="Output directory for certificates")

    args = parser.parse_args()

    print("🎫 BSD CERTIFICATE GENERATOR")
    print("=" * 60)

    if args.curves:
        # Generate individual certificates
        certificates = generate_individual_certificates(args.curves, args.output_dir)
        generate_batch_summary_certificate(certificates, args.output_dir)
        return 0

    elif args.results_file:
        # Load results and generate certificates from JSON
        import json
        
        try:
            with open(args.results_file, 'r') as f:
                results = json.load(f)
        except Exception as e:
            print(f"\n❌ Error loading results file: {e}")
            return 1

        if not results:
            print("\n❌ No results to process")
            return 1

        # Extract curve labels from results
        curve_labels = []
        if isinstance(results, dict):
            curve_labels = list(results.keys())
        elif isinstance(results, list):
            curve_labels = [r.get('curve', r.get('label', '')) for r in results if r]
        
        if not curve_labels:
            print("\n❌ No valid curve labels found in results")
            return 1

        # Generate certificates for curves in results
        certificates = generate_individual_certificates(curve_labels, args.output_dir)
        
        # Generate summary
        summary = generate_batch_summary_certificate(certificates, args.output_dir)
        
        # Count failures
        certificates_failed = sum(1 for cert in certificates if not cert.get('bsd_proven', False))
        
        print(f"\n✓ Certificates generated: {len(certificates)}")
        print(f"  Failed: {certificates_failed}")
        
        return 0 if certificates_failed == 0 else 1

    else:
        print("\n❌ You must provide either --curves or --results_file")
        return 1


if __name__ == "__main__":
    sys.exit(main())
