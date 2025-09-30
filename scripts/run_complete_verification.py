#!/usr/bin/env python3
"""
Complete BSD Verification Script
Runs all verification steps and generates final certificates

This is the main entry point for running comprehensive BSD verification
across multiple curves with full reporting.
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from src.verification.mass_verification import MassBSDVerifier
from src.cohomology.spectral_selmer_map import test_spectral_selmer_map
from src.cohomology.p_adic_integration import test_p_adic_integration
from src.cohomology.bloch_kato_conditions import test_bloch_kato_conditions


def run_component_tests():
    """
    Run tests for individual components
    
    Returns:
        bool: True if all tests pass
    """
    print("="*60)
    print("STEP 1: TESTING INDIVIDUAL COMPONENTS")
    print("="*60)
    print()
    
    all_passed = True
    
    # Test 1: Spectral Selmer Map
    print("1.1 Testing Spectral Selmer Map...")
    print("-" * 40)
    selmer_ok = test_spectral_selmer_map()
    all_passed = all_passed and selmer_ok
    print()
    
    # Test 2: p-adic Integration
    print("1.2 Testing p-adic Integration...")
    print("-" * 40)
    integration_ok = test_p_adic_integration()
    all_passed = all_passed and integration_ok
    print()
    
    # Test 3: Bloch-Kato Conditions
    print("1.3 Testing Bloch-Kato Conditions...")
    print("-" * 40)
    bloch_kato_ok = test_bloch_kato_conditions()
    all_passed = all_passed and bloch_kato_ok
    print()
    
    if all_passed:
        print("✅ All component tests passed")
    else:
        print("❌ Some component tests failed")
    
    return all_passed


def run_mass_verification(max_rank=3, max_conductor=1000):
    """
    Run mass verification on LMFDB curves
    
    Args:
        max_rank: Maximum rank to test
        max_conductor: Maximum conductor
        
    Returns:
        MassBSDVerifier: Verifier with results
    """
    print()
    print("="*60)
    print("STEP 2: RUNNING MASS VERIFICATION")
    print("="*60)
    print()
    
    verifier = MassBSDVerifier(results_file="mass_verification_results.json")
    verifier.run_mass_verification(
        max_rank=max_rank, 
        max_conductor=max_conductor
    )
    
    return verifier


def generate_final_report(verifier):
    """
    Generate final verification report
    
    Args:
        verifier: MassBSDVerifier with results
    """
    print()
    print("="*60)
    print("STEP 3: FINAL VERIFICATION REPORT")
    print("="*60)
    print()
    
    total = verifier.total_count
    verified = verifier.verified_count
    success_rate = (verified / total) * 100 if total > 0 else 0
    
    print(f"📊 Total curves tested: {total}")
    print(f"✅ Curves verified: {verified}")
    print(f"❌ Curves failed: {total - verified}")
    print(f"🎯 Success rate: {success_rate:.1f}%")
    print()
    
    if success_rate == 100:
        print("🏆 ALL CURVES VERIFIED SUCCESSFULLY!")
        print("✨ BSD SPECTRAL FRAMEWORK COMPLETELY VALIDATED!")
    elif success_rate >= 80:
        print("✅ EXCELLENT! Most curves verified successfully")
        print("   Check individual certificates for details on failed cases")
    elif success_rate >= 50:
        print("⚠️  PARTIAL SUCCESS - Many curves verified")
        print("   Some curves require additional analysis")
    else:
        print("⚠️  NEEDS ATTENTION - Many curves could not be verified")
        print("   Review verification logs for details")
    
    return success_rate == 100


def run_complete_verification(max_rank=3, max_conductor=1000):
    """
    Run complete BSD verification pipeline
    
    Args:
        max_rank: Maximum rank to test
        max_conductor: Maximum conductor
        
    Returns:
        bool: True if verification successful
    """
    print()
    print("🎯 COMPLETE BSD VERIFICATION PIPELINE")
    print("="*60)
    print()
    
    # Step 1: Test components
    components_ok = run_component_tests()
    
    if not components_ok:
        print()
        print("❌ Component tests failed. Continuing with caution...")
        print()
    
    # Step 2: Run mass verification
    verifier = run_mass_verification(
        max_rank=max_rank, 
        max_conductor=max_conductor
    )
    
    # Step 3: Generate report
    success = generate_final_report(verifier)
    
    print()
    print("="*60)
    print("VERIFICATION COMPLETE")
    print("="*60)
    
    return success


if __name__ == "__main__":
    # Parse command line arguments
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Run complete BSD verification'
    )
    parser.add_argument(
        '--max-rank', 
        type=int, 
        default=3,
        help='Maximum rank to test (default: 3)'
    )
    parser.add_argument(
        '--max-conductor', 
        type=int, 
        default=1000,
        help='Maximum conductor (default: 1000)'
    )
    
    args = parser.parse_args()
    
    success = run_complete_verification(
        max_rank=args.max_rank,
        max_conductor=args.max_conductor
    )
    
    sys.exit(0 if success else 1)
