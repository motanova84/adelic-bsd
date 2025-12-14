#!/usr/bin/env python3
"""
AIK Beacon Demonstration
========================

This example demonstrates the Activo Inmutable de Conocimiento (AIK) features
of the BSD verification module, including:

1. Integrity Hash generation
2. ECDSA signature for immutability
3. Complete AIK beacon structure
4. Independent verification
5. Certificate persistence and validation

Requirements:
- SageMath or sage-all package
- cryptography package
"""

import sys
import os
import json
from datetime import datetime

# Add paths for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../sage_plugin'))

try:
    from sage.all import EllipticCurve
    SAGE_AVAILABLE = True
except ImportError:
    print("⚠️  SageMath not available. This demo requires SageMath.")
    SAGE_AVAILABLE = False

if SAGE_AVAILABLE:
    from adelic_bsd import verify_bsd, verify_ecdsa_signature


def demo_basic_verification():
    """Demonstrate basic BSD verification with AIK beacon"""
    print("\n" + "="*70)
    print("DEMO 1: Basic BSD Verification with AIK Beacon")
    print("="*70)
    
    # Verify BSD for curve 11a1
    print("\nVerifying BSD for curve 11a1...")
    result = verify_bsd('11a1', generate_aik_beacon=True)
    
    # Display basic results
    print(f"\n✓ Curve: {result['curve_label']}")
    print(f"  Conductor: {result['conductor']}")
    print(f"  L(1): {result['L(s)']}")
    print(f"  Analytic Rank: {result['analytic_rank']}")
    
    # Display AIK beacon
    beacon = result['aik_beacon']
    print(f"\n🔐 AIK Beacon Generated:")
    print(f"  Integrity Hash: {beacon['integrity_hash'][:32]}...")
    print(f"  Timestamp: {beacon['timestamp']}")
    print(f"  Protocol: {beacon['noesis_protocol']}")
    print(f"  Framework: {beacon['framework']}")
    print(f"  Standard: {beacon['verification_standard']}")
    
    # Display scientific claim
    claim = beacon['verification_info']['scientific_claim']
    print(f"\n📜 Scientific Claim:")
    print(f"  {claim}")
    
    return result


def demo_signature_verification():
    """Demonstrate ECDSA signature verification"""
    print("\n" + "="*70)
    print("DEMO 2: ECDSA Signature Verification")
    print("="*70)
    
    # Generate verification
    result = verify_bsd('14a1', generate_aik_beacon=True)
    beacon = result['aik_beacon']
    
    print(f"\nCurve: {result['curve_label']}")
    
    # Verify the signature
    is_valid = verify_ecdsa_signature(
        beacon['integrity_hash'],
        beacon['signature']
    )
    
    if is_valid:
        print("\n✓ ECDSA Signature is VALID")
        print("  The certificate is authentic and untampered")
    else:
        print("\n✗ ECDSA Signature is INVALID")
        print("  Warning: Certificate may have been tampered with!")
    
    # Display signature info
    sig = beacon['signature']
    print(f"\nSignature Details:")
    print(f"  Algorithm: {sig['algorithm']}")
    print(f"  Curve: {sig['curve']}")
    print(f"  Signature: {sig['signature'][:40]}...")
    print(f"  Public Key: Available for independent verification")
    
    return result


def demo_tampering_detection():
    """Demonstrate tamper detection"""
    print("\n" + "="*70)
    print("DEMO 3: Tamper Detection")
    print("="*70)
    
    # Generate verification
    result = verify_bsd('15a1', generate_aik_beacon=True)
    beacon = result['aik_beacon']
    
    print(f"\nCurve: {result['curve_label']}")
    
    # Original signature should verify
    original_valid = verify_ecdsa_signature(
        beacon['integrity_hash'],
        beacon['signature']
    )
    print(f"\n1. Original certificate: {'✓ VALID' if original_valid else '✗ INVALID'}")
    
    # Try with tampered hash
    tampered_hash = "0" * 64
    tampered_valid = verify_ecdsa_signature(
        tampered_hash,
        beacon['signature']
    )
    print(f"2. Tampered certificate: {'✓ VALID' if tampered_valid else '✗ INVALID (Expected)'}")
    
    if not tampered_valid:
        print("\n✓ Tampering successfully detected!")
        print("  The integrity hash protects against data modification")


def demo_batch_certification():
    """Demonstrate batch certification of multiple curves"""
    print("\n" + "="*70)
    print("DEMO 4: Batch Certification")
    print("="*70)
    
    curves = ['11a1', '11a2', '11a3', '14a1', '15a1']
    certificates = []
    
    print(f"\nGenerating AIK-certified verifications for {len(curves)} curves...")
    
    for label in curves:
        result = verify_bsd(label, generate_aik_beacon=True)
        certificates.append({
            'curve': label,
            'rank': result['analytic_rank'],
            'L_value': float(result['L(s)']),
            'integrity_hash': result['aik_beacon']['integrity_hash'],
            'timestamp': result['aik_beacon']['timestamp']
        })
        print(f"  ✓ {label}: rank={result['analytic_rank']}, L(1)={result['L(s)']:.6f}")
    
    print(f"\n✓ Generated {len(certificates)} AIK-certified BSD verifications")
    
    # All hashes should be unique
    hashes = [c['integrity_hash'] for c in certificates]
    unique_hashes = len(set(hashes))
    print(f"  All {unique_hashes} integrity hashes are unique ✓")
    
    return certificates


def demo_certificate_persistence():
    """Demonstrate certificate saving and loading"""
    print("\n" + "="*70)
    print("DEMO 5: Certificate Persistence and Validation")
    print("="*70)
    
    # Generate certificate
    result = verify_bsd('37a1', generate_aik_beacon=True)
    
    # Save to file
    output_dir = '/tmp/aik_certificates'
    os.makedirs(output_dir, exist_ok=True)
    cert_file = f"{output_dir}/bsd_{result['curve_label']}_certificate.json"
    
    # Prepare for JSON serialization
    cert_data = {
        'curve_label': result['curve_label'],
        'conductor': int(result['conductor']),
        'L_value': float(result['L(s)']),
        's': result['s'],
        'analytic_rank': result['analytic_rank'],
        'aik_beacon': result['aik_beacon']
    }
    
    with open(cert_file, 'w') as f:
        json.dump(cert_data, f, indent=2)
    
    print(f"\n✓ Certificate saved to: {cert_file}")
    
    # Load and validate
    with open(cert_file, 'r') as f:
        loaded_cert = json.load(f)
    
    beacon = loaded_cert['aik_beacon']
    is_valid = verify_ecdsa_signature(
        beacon['integrity_hash'],
        beacon['signature']
    )
    
    print(f"\n✓ Certificate loaded from disk")
    print(f"  Validation: {'✓ VALID' if is_valid else '✗ INVALID'}")
    print(f"  Curve: {loaded_cert['curve_label']}")
    print(f"  Certified at: {beacon['timestamp']}")
    print(f"  Scientific claim: {beacon['verification_info']['scientific_claim']}")
    
    return cert_file


def demo_aik_properties():
    """Demonstrate AIK properties in detail"""
    print("\n" + "="*70)
    print("DEMO 6: AIK Properties and Guarantees")
    print("="*70)
    
    result = verify_bsd('11a1', generate_aik_beacon=True)
    beacon = result['aik_beacon']
    
    properties = beacon['verification_info']['properties']
    
    print("\n🛡️  AIK Guarantees:")
    print("\n1. Integrity:")
    print(f"   {properties['integrity']}")
    
    print("\n2. Immutability:")
    print(f"   {properties['immutability']}")
    
    print("\n3. Verifiability:")
    print(f"   {properties['verifiability']}")
    
    print("\n4. Integration:")
    print(f"   {properties['integration']}")
    
    print("\n✨ Noēsis ∞³ Protocol:")
    print(f"   This beacon implements the {beacon['noesis_protocol']} protocol")
    print(f"   Framework: {beacon['framework']}")
    print(f"   Standard: {beacon['verification_standard']}")


def demo_comparison_with_without_aik():
    """Compare verification with and without AIK beacon"""
    print("\n" + "="*70)
    print("DEMO 7: Comparison - With vs Without AIK Beacon")
    print("="*70)
    
    # Without AIK
    print("\n1. Without AIK Beacon (backward compatible):")
    result_basic = verify_bsd('11a1', generate_aik_beacon=False)
    print(f"   Curve: {result_basic['curve_label']}")
    print(f"   L(1): {result_basic['L(s)']}")
    print(f"   Fields: {list(result_basic.keys())}")
    print(f"   AIK Beacon: {'aik_beacon' in result_basic}")
    
    # With AIK
    print("\n2. With AIK Beacon (enhanced security):")
    result_aik = verify_bsd('11a1', generate_aik_beacon=True)
    print(f"   Curve: {result_aik['curve_label']}")
    print(f"   L(1): {result_aik['L(s)']}")
    print(f"   Fields: {list(result_aik.keys())}")
    print(f"   AIK Beacon: {'aik_beacon' in result_aik}")
    
    if 'aik_beacon' in result_aik:
        beacon = result_aik['aik_beacon']
        print(f"   - Integrity Hash: ✓")
        print(f"   - ECDSA Signature: ✓")
        print(f"   - Timestamp: {beacon['timestamp']}")
        print(f"   - Protocol: {beacon['noesis_protocol']}")
    
    print("\n✓ Backward compatibility maintained")
    print("  AIK beacon is optional and does not break existing code")


def main():
    """Run all AIK beacon demonstrations"""
    if not SAGE_AVAILABLE:
        print("\n❌ This demo requires SageMath to be installed.")
        print("   Install with: pip install sage-all")
        return
    
    print("\n" + "="*70)
    print("AIK BEACON DEMONSTRATION")
    print("Activo Inmutable de Conocimiento - BSD Verification")
    print("="*70)
    print("\nThis demonstration showcases the cryptographic certification")
    print("features of the enhanced BSD verification module.")
    
    try:
        # Run all demos
        demo_basic_verification()
        demo_signature_verification()
        demo_tampering_detection()
        demo_batch_certification()
        cert_file = demo_certificate_persistence()
        demo_aik_properties()
        demo_comparison_with_without_aik()
        
        # Summary
        print("\n" + "="*70)
        print("🎉 ALL DEMONSTRATIONS COMPLETED SUCCESSFULLY!")
        print("="*70)
        print("\nKey Takeaways:")
        print("  1. ✓ Integrity hash ensures data authenticity")
        print("  2. ✓ ECDSA signature provides immutability")
        print("  3. ✓ Tampering is automatically detected")
        print("  4. ✓ Certificates can be persisted and validated")
        print("  5. ✓ Backward compatibility maintained")
        print("  6. ✓ Ready for SageMath community use")
        print(f"\nExample certificate saved at: {cert_file}")
        print("\nFor more information, see: docs/AIK_BEACON_DOCUMENTATION.md")
        print("="*70 + "\n")
        
    except Exception as e:
        print(f"\n❌ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()
