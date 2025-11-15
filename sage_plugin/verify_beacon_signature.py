#!/usr/bin/env python3
"""
QCAL Beacon Signature Verification

This script demonstrates how to verify the ECDSA signature of a QCAL Beacon.

Usage:
    python3 verify_beacon_signature.py <beacon_file.json>

Example:
    python3 verify_beacon_signature.py beacons/qcal_beacon_bsd_11a1.json
"""

import sys
import json
from pathlib import Path

from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.backends import default_backend
from cryptography.exceptions import InvalidSignature


def verify_beacon(beacon_file):
    """
    Verify the ECDSA signature of a QCAL Beacon
    
    Args:
        beacon_file: Path to the beacon JSON file
        
    Returns:
        bool: True if signature is valid, False otherwise
    """
    # Read beacon file
    with open(beacon_file, 'r') as f:
        beacon = json.load(f)
    
    qcal = beacon["qcal_beacon"]
    
    print(f"\n{'='*60}")
    print("  QCAL Beacon Signature Verification")
    print(f"{'='*60}\n")
    
    print(f"Beacon ID:        {qcal['id']}")
    print(f"Curve:            {qcal['curve']}")
    print(f"Timestamp:        {qcal['timestamp']}")
    print(f"Validator:        {qcal['validator_node']}")
    
    # Extract signature and public key
    signature_hex = qcal['signature']['signature_hex']
    signature = bytes.fromhex(signature_hex)
    public_key_pem = qcal['public_key_pem']
    message_signed = qcal['message_signed']
    
    print(f"\nMessage:          {message_signed[:50]}...")
    print(f"Signature (hex):  {signature_hex[:32]}...")
    
    # Load public key from PEM
    public_key = serialization.load_pem_public_key(
        public_key_pem.encode(),
        backend=default_backend()
    )
    
    print(f"\n{'='*60}")
    print("  Verifying Signature...")
    print(f"{'='*60}\n")
    
    # Verify signature
    try:
        public_key.verify(
            signature,
            message_signed.encode(),
            ec.ECDSA(hashes.SHA3_256())
        )
        print("✅ SIGNATURE VALID")
        print("\nThe beacon signature is authentic and the data has not been tampered with.")
        return True
    except InvalidSignature:
        print("❌ SIGNATURE INVALID")
        print("\nThe beacon signature is invalid or the data has been modified.")
        return False
    except Exception as e:
        print(f"❌ ERROR: {e}")
        return False


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 verify_beacon_signature.py <beacon_file.json>")
        print("\nExample:")
        print("  python3 verify_beacon_signature.py beacons/qcal_beacon_bsd_11a1.json")
        sys.exit(1)
    
    beacon_file = Path(sys.argv[1])
    
    if not beacon_file.exists():
        print(f"Error: File not found: {beacon_file}")
        sys.exit(1)
    
    try:
        is_valid = verify_beacon(beacon_file)
        sys.exit(0 if is_valid else 1)
    except Exception as e:
        print(f"\nError: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
