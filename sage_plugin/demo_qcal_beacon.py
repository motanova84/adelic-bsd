#!/usr/bin/env sage -python
"""
Demo script for QCAL Beacon generation

This script demonstrates how to use the adelic_bsd module to:
1. Verify the BSD conjecture for an elliptic curve
2. Generate a cryptographically signed QCAL Beacon

Usage:
    sage -python demo_qcal_beacon.py [curve_label]

Example:
    sage -python demo_qcal_beacon.py 11a1
    sage -python demo_qcal_beacon.py 37a1
"""

import sys
from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd


def main():
    # Default curve if none provided
    curve_label = sys.argv[1] if len(sys.argv) > 1 else "11a1"
    
    print(f"\n{'='*60}")
    print(f"  QCAL Beacon Generator for BSD Verification")
    print(f"{'='*60}\n")
    print(f"Generating beacon for curve: {curve_label}\n")
    
    try:
        # Generate the beacon
        beacon = generate_qcal_beacon_for_bsd(curve_label)
        
        print(f"\n{'='*60}")
        print("  Beacon Summary")
        print(f"{'='*60}")
        
        qcal = beacon["qcal_beacon"]
        print(f"Beacon ID:        {qcal['id']}")
        print(f"Timestamp:        {qcal['timestamp']}")
        print(f"Curve:            {qcal['curve']}")
        print(f"L(1):             {qcal['L_at_1']}")
        print(f"Analytic Rank:    {qcal['analytic_rank']}")
        print(f"Integrity Hash:   {qcal['integrity_hash'][:16]}...")
        print(f"Validator:        {qcal['validator_node']}")
        print(f"Signature:        {qcal['signature']['signature_hex'][:32]}...")
        
        print(f"\n{'='*60}\n")
        print("✅ Beacon generation completed successfully!")
        print("\nThe beacon has been saved to:")
        print(f"   sage_plugin/beacons/qcal_beacon_bsd_{curve_label.replace('/', '_')}.json")
        print("\n")
        
    except Exception as e:
        print(f"\n❌ Error generating beacon: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
