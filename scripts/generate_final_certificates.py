#!/usr/bin/env python3
"""
Generate Final Certificates
Creates formal BSD certificates for verified curves

This script reads verification results and generates both JSON and
human-readable text certificates for each verified curve.
"""

import sys
import os
import json

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from sage.all import EllipticCurve
from src.verification.certificate_generator import BSDCertificateGenerator


def load_verification_results(results_file="mass_verification_results.json"):
    """
    Load verification results from file
    
    Args:
        results_file: Path to results JSON
        
    Returns:
        dict: Verification results
    """
    try:
        with open(results_file, 'r') as f:
            results = json.load(f)
        print(f"📖 Loaded {len(results)} verification results")
        return results
    except FileNotFoundError:
        print(f"❌ Results file not found: {results_file}")
        print("   Run run_complete_verification.py first")
        return {}
    except Exception as e:
        print(f"❌ Error loading results: {e}")
        return {}


def generate_certificates_for_all(results, output_dir="certificates"):
    """
    Generate certificates for all curves in results
    
    Args:
        results: Verification results dict
        output_dir: Output directory for certificates
        
    Returns:
        dict: Statistics about generated certificates
    """
    generator = BSDCertificateGenerator(output_dir=output_dir)
    
    stats = {
        'total': len(results),
        'verified': 0,
        'certificates_generated': 0,
        'certificates_failed': 0
    }
    
    print(f"\n🎫 Generating certificates for {stats['total']} curves...")
    print("="*60)
    
    for label, verification_data in results.items():
        try:
            # Load the curve
            E = EllipticCurve(label)
            
            # Track verification status
            if verification_data.get('bsd_verified', False):
                stats['verified'] += 1
            
            # Generate certificate
            print(f"\n📄 Generating certificate for {label}...")
            certificate = generator.generate_certificate(E, verification_data)
            
            # Save JSON certificate
            json_file = generator.save_certificate(certificate)
            
            # Save text certificate
            text_file = generator.save_text_certificate(certificate)
            
            if json_file and text_file:
                stats['certificates_generated'] += 1
            else:
                stats['certificates_failed'] += 1
                
        except Exception as e:
            print(f"⚠️  Error generating certificate for {label}: {e}")
            stats['certificates_failed'] += 1
    
    return stats


def print_final_summary(stats):
    """
    Print summary of certificate generation
    
    Args:
        stats: Statistics dict
    """
    print("\n" + "="*60)
    print("📊 CERTIFICATE GENERATION SUMMARY")
    print("="*60)
    print(f"Total curves processed: {stats['total']}")
    print(f"Curves with BSD verified: {stats['verified']}")
    print(f"Certificates generated: {stats['certificates_generated']}")
    
    if stats['certificates_failed'] > 0:
        print(f"Failed to generate: {stats['certificates_failed']}")
    
    success_rate = (stats['certificates_generated'] / stats['total'] * 100 
                   if stats['total'] > 0 else 0)
    print(f"\nGeneration success rate: {success_rate:.1f}%")
    
    if success_rate == 100:
        print("\n✅ All certificates generated successfully!")
    else:
        print(f"\n⚠️  Some certificates could not be generated")
    
    print("="*60)


def main():
    """Main execution function"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Generate BSD verification certificates'
    )
    parser.add_argument(
        '--results-file',
        type=str,
        default='mass_verification_results.json',
        help='Path to verification results JSON (default: mass_verification_results.json)'
    )
    parser.add_argument(
        '--output-dir',
        type=str,
        default='certificates',
        help='Output directory for certificates (default: certificates)'
    )
    
    args = parser.parse_args()
    
    print("🎫 BSD CERTIFICATE GENERATOR")
    print("="*60)
    
    # Load results
    results = load_verification_results(args.results_file)
    
    if not results:
        print("\n❌ No results to process")
        return 1
    
    # Generate certificates
    stats = generate_certificates_for_all(results, args.output_dir)
    
    # Print summary
    print_final_summary(stats)
    
    return 0 if stats['certificates_failed'] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
