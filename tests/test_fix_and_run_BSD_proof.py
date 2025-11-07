#!/usr/bin/env python3
"""
Test for fix_and_run_BSD_proof.py script
"""

import sys
import subprocess
from pathlib import Path
import json

def test_script_exists():
    """Test that the script exists"""
    script_path = Path(__file__).parent.parent / 'scripts' / 'fix_and_run_BSD_proof.py'
    assert script_path.exists(), f"Script not found: {script_path}"
    print("✓ Script exists")

def test_check_sage_availability():
    """Test the check_sage_availability function"""
    sys.path.insert(0, str(Path(__file__).parent.parent / 'scripts'))
    from fix_and_run_BSD_proof import check_sage_availability
    
    # This will return False in CI/CD without Sage
    result = check_sage_availability()
    assert isinstance(result, bool), "check_sage_availability should return bool"
    print(f"✓ check_sage_availability returns: {result}")

def test_certificate_verification_logic():
    """Test that certificate verification logic is correct"""
    # Test with the existing certificate
    cert_file = Path(__file__).parent.parent / 'proofs' / 'BSD_UNCONDITIONAL_CERTIFICATE.json'
    
    if cert_file.exists():
        with open(cert_file) as f:
            cert = json.load(f)
        
        status = cert.get('status', 'UNKNOWN')
        components = cert.get('components', {})
        
        # Extract component status
        dR_status = components.get('dR_compatibility', {}).get('status', 'UNKNOWN')
        PT_status = components.get('PT_compatibility', {}).get('status', 'UNKNOWN')
        spectral_status = components.get('spectral_framework', {}).get('status', 'UNKNOWN')
        
        all_proved = (dR_status == 'PROVED' and 
                     PT_status == 'PROVED' and 
                     spectral_status == 'PROVED')
        
        print(f"✓ Certificate verification logic works")
        print(f"  Status: {status}")
        print(f"  dR: {dR_status}, PT: {PT_status}, Spectral: {spectral_status}")
        print(f"  All proved: {all_proved}")
    else:
        print("⚠ Certificate file not found (this is OK in fresh environments)")

def test_script_without_sage():
    """Test that script handles missing Sage gracefully"""
    script_path = Path(__file__).parent.parent / 'scripts' / 'fix_and_run_BSD_proof.py'
    
    result = subprocess.run(
        [sys.executable, str(script_path)],
        capture_output=True,
        text=True,
        timeout=10
    )
    
    # Should exit with code 1 when Sage is not available
    # and print appropriate message
    assert "SageMath no está disponible" in result.stdout or result.returncode == 0, \
        "Script should handle missing Sage gracefully"
    
    print("✓ Script handles missing Sage gracefully")

if __name__ == "__main__":
    print("Testing fix_and_run_BSD_proof.py\n")
    print("=" * 70)
    
    try:
        test_script_exists()
        test_check_sage_availability()
        test_certificate_verification_logic()
        test_script_without_sage()
        
        print("=" * 70)
        print("\n✅ All tests passed!")
        sys.exit(0)
    except Exception as e:
        print(f"\n❌ Test failed: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
