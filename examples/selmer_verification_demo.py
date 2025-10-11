"""
Selmer Map Verification Demo
Demonstrates the Selmer verification module for BSD framework

This script shows how to:
1. Verify Selmer maps for individual curves
2. Generate verification certificates
3. Batch verify multiple curves
4. Generate verification reports
"""

from sage.all import EllipticCurve
import sys
import os

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.verification import (
    SelmerVerification,
    verify_selmer_maps,
    batch_verify_selmer_maps,
    generate_selmer_verification_report
)


def demo_single_curve_verification():
    """Demonstrate verification of Selmer maps for a single curve"""
    print("\n" + "="*70)
    print("DEMO 1: SINGLE CURVE SELMER VERIFICATION")
    print("="*70)
    
    curve_label = '11a1'
    print(f"\nVerifying Selmer maps for curve {curve_label}...")
    
    E = EllipticCurve(curve_label)
    print(f"Curve: {E}")
    print(f"Conductor: {E.conductor()}")
    print(f"Rank: {E.rank()}")
    
    # Create verifier with specific primes
    print("\nInitializing SelmerVerification...")
    verifier = SelmerVerification(E, primes=[2, 3], precision=20)
    
    # Run complete verification
    print("\nRunning complete verification...")
    certificate = verifier.verify_all()
    
    # Print summary
    verifier.print_verification_summary()
    
    return certificate


def demo_convenience_function():
    """Demonstrate the convenience function for quick verification"""
    print("\n" + "="*70)
    print("DEMO 2: QUICK VERIFICATION WITH CONVENIENCE FUNCTION")
    print("="*70)
    
    curve_label = '37a1'
    print(f"\nQuick verification of {curve_label}...")
    
    E = EllipticCurve(curve_label)
    
    # Use convenience function (auto-selects conductor primes)
    certificate = verify_selmer_maps(E, precision=20)
    
    print(f"\nCurve: {certificate['curve']}")
    print(f"Primes verified: {certificate['primes_verified']}")
    print(f"Verification passed: {'✓' if certificate['verification_passed'] else '✗'}")
    
    # Print detailed steps
    print("\nVerification steps:")
    for step_name, step_data in certificate['verification_steps'].items():
        if isinstance(step_data, dict):
            passed = step_data.get('all_initialized') or step_data.get('all_verified') or step_data.get('compatible', False)
            status = '✓' if passed else '✗'
            print(f"  {status} {step_name}")
    
    return certificate


def demo_batch_verification():
    """Demonstrate batch verification of multiple curves"""
    print("\n" + "="*70)
    print("DEMO 3: BATCH VERIFICATION")
    print("="*70)
    
    # Select a set of curves with different properties
    curve_labels = ['11a1', '37a1', '389a1', '5077a1']
    
    print(f"\nBatch verifying {len(curve_labels)} curves:")
    for label in curve_labels:
        E = EllipticCurve(label)
        print(f"  - {label}: rank {E.rank()}, conductor {E.conductor()}")
    
    print("\nRunning batch verification (this may take a moment)...")
    results = batch_verify_selmer_maps(
        curve_labels,
        primes=[2],  # Verify at p=2 for all curves
        precision=20
    )
    
    print("\nBatch verification results:")
    print(f"Total curves: {results['total_curves']}")
    print(f"Passed: {results['passed']}")
    print(f"Failed: {results['failed']}")
    print(f"Success rate: {results['success_rate']}")
    
    print("\nIndividual results:")
    for label, cert in results['results'].items():
        status = '✓' if cert.get('verification_passed', False) else '✗'
        print(f"  {status} {label}")
    
    return results


def demo_certificate_generation():
    """Demonstrate certificate generation and saving"""
    print("\n" + "="*70)
    print("DEMO 4: CERTIFICATE GENERATION")
    print("="*70)
    
    curve_label = '11a1'
    print(f"\nGenerating verification certificate for {curve_label}...")
    
    E = EllipticCurve(curve_label)
    verifier = SelmerVerification(E, primes=[2, 3])
    
    # Generate and save certificate
    certificate = verifier.generate_certificate(save=True, output_dir='certificates')
    
    print(f"\nCertificate generated:")
    print(f"  Type: {certificate['certificate_type']}")
    print(f"  Version: {certificate['certificate_version']}")
    print(f"  Curve: {certificate['curve']}")
    print(f"  Verified: {'✓' if certificate['verification_passed'] else '✗'}")
    print(f"  Hash: {certificate['certificate_hash'][:16]}...")
    
    if 'saved_to' in certificate:
        print(f"  Saved to: {certificate['saved_to']}")
    
    return certificate


def demo_verification_report():
    """Demonstrate verification report generation"""
    print("\n" + "="*70)
    print("DEMO 5: VERIFICATION REPORT GENERATION")
    print("="*70)
    
    # Single curve report
    print("\n--- Single Curve Report ---")
    E = EllipticCurve('11a1')
    certificate = verify_selmer_maps(E, primes=[2])
    
    report = generate_selmer_verification_report(certificate)
    print(report)
    
    # Batch report
    print("\n--- Batch Report ---")
    curve_labels = ['11a1', '37a1', '389a1']
    batch_results = batch_verify_selmer_maps(curve_labels, primes=[2])
    
    batch_report = generate_selmer_verification_report(batch_results)
    print(batch_report)


def demo_integration_with_bsd_prover():
    """Demonstrate integration with formal BSD prover"""
    print("\n" + "="*70)
    print("DEMO 6: INTEGRATION WITH FORMAL BSD PROVER")
    print("="*70)
    
    curve_label = '11a1'
    print(f"\nDemonstrating integrated workflow for {curve_label}...")
    
    E = EllipticCurve(curve_label)
    
    # Step 1: Verify Selmer maps
    print("\nStep 1: Verifying Selmer maps...")
    selmer_cert = verify_selmer_maps(E, primes=[2, 3])
    print(f"  Selmer verification: {'✓ PASSED' if selmer_cert['verification_passed'] else '✗ FAILED'}")
    
    # Step 2: Run formal BSD prover (if Selmer maps verified)
    if selmer_cert['verification_passed']:
        print("\nStep 2: Running formal BSD prover...")
        try:
            from src.verification import FormalBSDProver
            prover = FormalBSDProver(E, proof_level="basic")
            
            print("  Formal BSD prover initialized")
            print(f"  Curve: {prover.certificate['metadata']['curve']}")
            print(f"  Rank: {prover.certificate['metadata']['rank']}")
            
            print("\n✓ Integration successful!")
            print("  Selmer maps verified and compatible with BSD framework")
        except Exception as e:
            print(f"  Note: {e}")
    else:
        print("\n⚠ Selmer verification failed, skipping BSD prover")


def run_all_demos():
    """Run all demonstration examples"""
    print("\n" + "="*70)
    print("SELMER MAP VERIFICATION - COMPLETE DEMONSTRATION")
    print("="*70)
    print("\nThis demo showcases the Selmer verification module")
    print("added to the adelic-bsd framework.")
    
    demos = [
        ("Single Curve Verification", demo_single_curve_verification),
        ("Quick Verification", demo_convenience_function),
        ("Batch Verification", demo_batch_verification),
        ("Certificate Generation", demo_certificate_generation),
        ("Verification Reports", demo_verification_report),
        ("Integration with BSD Prover", demo_integration_with_bsd_prover),
    ]
    
    results = []
    for name, demo_func in demos:
        try:
            print(f"\n\nRunning demo: {name}...")
            result = demo_func()
            results.append((name, True, result))
        except Exception as e:
            print(f"\n✗ Demo failed: {e}")
            import traceback
            traceback.print_exc()
            results.append((name, False, None))
    
    # Summary
    print("\n\n" + "="*70)
    print("DEMO SUMMARY")
    print("="*70)
    
    for name, success, _ in results:
        status = "✓ SUCCESS" if success else "✗ FAILED"
        print(f"{status}: {name}")
    
    successful = sum(1 for _, s, _ in results if s)
    total = len(results)
    print(f"\nTotal: {successful}/{total} demos completed successfully")
    print("="*70 + "\n")


if __name__ == "__main__":
    print("\nStarting Selmer Map Verification Demo...")
    print("This demonstrates the new verification module for spectral Selmer maps.")
    
    try:
        run_all_demos()
        print("\n✓ All demos completed!")
    except Exception as e:
        print(f"\n✗ Error running demos: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
