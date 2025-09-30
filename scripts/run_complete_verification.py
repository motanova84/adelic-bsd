#!/usr/bin/env python3
"""
Complete Verification Runner
Executes full BSD verification system on test curves

This script runs the complete spectral BSD verification framework,
testing all components: operators, cohomology, heights, and verification.
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve
from src.spectral_bsd import SpectralBSD
from src.verification import FormalBSDProver
from src.verification.mass_verification import batch_verify_bsd


def run_single_verification(curve_label):
    """
    Run complete verification for a single curve
    
    Args:
        curve_label: Curve label (e.g., '11a1')
    """
    print(f"\n{'='*70}")
    print(f"VERIFYING CURVE: {curve_label}")
    print(f"{'='*70}\n")
    
    try:
        # Load curve
        E = EllipticCurve(curve_label)
        print(f"✓ Curve loaded: {curve_label}")
        print(f"  Conductor: {E.conductor()}")
        print(f"  Rank: {E.rank()}")
        
        # Initialize spectral BSD framework
        print("\n1. Initializing Spectral BSD Framework...")
        spectral = SpectralBSD(E)
        print("✓ Framework initialized")
        
        # Compute spectral rank
        print("\n2. Computing Spectral Rank...")
        rank_data = spectral.compute_spectral_rank()
        print(f"✓ Spectral rank: {rank_data['spectral_rank']}")
        print(f"✓ Algebraic rank: {rank_data['algebraic_rank']}")
        print(f"✓ Ranks match: {rank_data['ranks_match']}")
        
        # Verify BSD formula
        print("\n3. Verifying BSD Formula...")
        bsd_verification = spectral.verify_bsd_formula()
        print(f"✓ SHA finite: {bsd_verification['sha_bound']['finiteness_proved']}")
        print(f"✓ SHA bound: {bsd_verification['sha_bound']['global_bound']}")
        
        # Generate formal certificate
        print("\n4. Generating Formal Certificate...")
        prover = FormalBSDProver(E)
        certificate = prover.prove_bsd_completely()
        print(f"✓ BSD proven: {certificate.get('bsd_proven', False)}")
        
        # Summary
        print(f"\n{'='*70}")
        print("VERIFICATION SUMMARY")
        print(f"{'='*70}")
        print(f"Curve: {curve_label}")
        print(f"Ranks Compatible: {rank_data['ranks_match']}")
        print(f"SHA Finite: {bsd_verification['sha_bound']['finiteness_proved']}")
        print(f"BSD Proven: {certificate.get('bsd_proven', False)}")
        print(f"{'='*70}\n")
        
        return True
        
    except Exception as e:
        print(f"\n✗ Error during verification: {e}")
        import traceback
        traceback.print_exc()
        return False


def run_batch_verification(curve_labels):
    """
    Run batch verification for multiple curves
    
    Args:
        curve_labels: List of curve labels
    """
    print(f"\n{'='*70}")
    print(f"BATCH VERIFICATION: {len(curve_labels)} curves")
    print(f"{'='*70}\n")
    
    try:
        results = batch_verify_bsd(curve_labels, save_certificates=True)
        
        # Summary
        successful = sum(1 for r in results.values() if r.get('bsd_proven', False))
        total = len(results)
        
        print(f"\n{'='*70}")
        print("BATCH VERIFICATION SUMMARY")
        print(f"{'='*70}")
        print(f"Total curves: {total}")
        print(f"Successful: {successful}")
        print(f"Failed: {total - successful}")
        print(f"Success rate: {(successful/total*100):.1f}%")
        
        # Details
        print("\nDetailed Results:")
        for label, result in results.items():
            status = "✓" if result.get('bsd_proven', False) else "✗"
            print(f"  {status} {label}")
        
        print(f"{'='*70}\n")
        
        return results
        
    except Exception as e:
        print(f"\n✗ Error during batch verification: {e}")
        import traceback
        traceback.print_exc()
        return None


def run_complete_test_suite():
    """
    Run complete test suite on standard curves
    """
    print("\n" + "="*70)
    print("COMPLETE BSD VERIFICATION SYSTEM")
    print("="*70)
    
    # Test curves covering different ranks and reduction types
    test_curves = [
        '11a1',   # Rank 0, conductor 11
        '37a1',   # Rank 1, conductor 37
        '389a1',  # Rank 2, conductor 389
        '5077a1', # Rank 3, conductor 5077
    ]
    
    print(f"\nTest curves: {', '.join(test_curves)}")
    
    # Run individual verifications
    print("\n" + "="*70)
    print("PHASE 1: Individual Verifications")
    print("="*70)
    
    for label in test_curves[:2]:  # Test first 2 in detail
        run_single_verification(label)
    
    # Run batch verification
    print("\n" + "="*70)
    print("PHASE 2: Batch Verification")
    print("="*70)
    
    run_batch_verification(test_curves)
    
    print("\n" + "="*70)
    print("VERIFICATION COMPLETE")
    print("="*70)
    print("\nCertificates saved in: certificates/")
    print("="*70 + "\n")


def main():
    """Main entry point"""
    if len(sys.argv) > 1:
        # Run on specified curves
        curve_labels = sys.argv[1:]
        
        if len(curve_labels) == 1:
            run_single_verification(curve_labels[0])
        else:
            run_batch_verification(curve_labels)
    else:
        # Run complete test suite
        run_complete_test_suite()


if __name__ == "__main__":
    main()
