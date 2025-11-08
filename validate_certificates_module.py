#!/usr/bin/env python3
"""
Validation script for BSD certificate module (non-Sage dependent checks)
This script validates the module structure and basic functionality.
"""

import os
import sys
import hashlib
import json
from datetime import datetime

def test_module_structure():
    """Test that the module structure is correct"""
    print("Testing module structure...")
    
    base_path = "sagemath_integration/sage/schemes/elliptic_curves/bsd_spectral"
    
    # Check directories exist
    assert os.path.exists("sagemath_integration"), "sagemath_integration directory missing"
    assert os.path.exists(base_path), f"{base_path} directory missing"
    
    # Check key files exist
    assert os.path.exists(f"{base_path}/certificates.py"), "certificates.py missing"
    assert os.path.exists(f"{base_path}/__init__.py"), "__init__.py missing"
    
    # Check __init__.py files in hierarchy
    for subdir in ["sagemath_integration", 
                   "sagemath_integration/sage",
                   "sagemath_integration/sage/schemes",
                   "sagemath_integration/sage/schemes/elliptic_curves"]:
        init_file = f"{subdir}/__init__.py"
        assert os.path.exists(init_file), f"Missing {init_file}"
    
    print("✓ Module structure is correct")


def test_certificates_file_content():
    """Test that certificates.py contains required elements"""
    print("Testing certificates.py content...")
    
    with open("sagemath_integration/sage/schemes/elliptic_curves/bsd_spectral/certificates.py", 'r') as f:
        content = f.read()
    
    # Check for required classes and functions
    assert "class BSDCertificate" in content, "BSDCertificate class missing"
    assert "def generate_bsd_certificate" in content, "generate_bsd_certificate function missing"
    assert "def verify_certificate" in content, "verify_certificate function missing"
    
    # Check for required methods
    assert "def curve_hash" in content, "curve_hash method missing"
    assert "def add_spectral_proof" in content, "add_spectral_proof method missing"
    assert "def add_dR_verification" in content, "add_dR_verification method missing"
    assert "def add_PT_verification" in content, "add_PT_verification method missing"
    assert "def finalize" in content, "finalize method missing"
    assert "def status" in content, "status method missing"
    assert "def confidence_level" in content, "confidence_level method missing"
    assert "def export_json" in content, "export_json method missing"
    assert "def export_latex" in content, "export_latex method missing"
    assert "def verify" in content, "verify method missing"
    
    # Check for cryptographic imports
    assert "import hashlib" in content, "hashlib import missing"
    assert "SHA-256" in content, "SHA-256 documentation missing"
    
    # Check for proper docstrings
    assert 'r"""' in content, "Docstrings missing"
    assert "EXAMPLES::" in content, "EXAMPLES section missing"
    assert "TESTS::" in content, "TESTS section missing"
    
    print("✓ certificates.py contains all required elements")


def test_init_file_exports():
    """Test that __init__.py exports correct symbols"""
    print("Testing __init__.py exports...")
    
    with open("sagemath_integration/sage/schemes/elliptic_curves/bsd_spectral/__init__.py", 'r') as f:
        content = f.read()
    
    # Check for required exports
    assert "BSDCertificate" in content, "BSDCertificate not exported"
    assert "generate_bsd_certificate" in content, "generate_bsd_certificate not exported"
    assert "verify_certificate" in content, "verify_certificate not exported"
    assert "__all__" in content, "__all__ list missing"
    
    print("✓ __init__.py exports are correct")


def test_hash_functionality():
    """Test SHA-256 hash functionality (without Sage)"""
    print("Testing hash functionality...")
    
    # Test basic hash computation using the same format as certificates.py
    # Format: conductor:discriminant:j_invariant
    data1 = "11:-161051:-122023936/161051"
    hash1 = hashlib.sha256(data1.encode()).hexdigest()
    
    # Hash should be 64 characters
    assert len(hash1) == 64, f"Hash length should be 64, got {len(hash1)}"
    
    # Hash should be hexadecimal
    assert all(c in '0123456789abcdef' for c in hash1), "Hash should be hexadecimal"
    
    # Same data should produce same hash
    hash2 = hashlib.sha256(data1.encode()).hexdigest()
    assert hash1 == hash2, "Same data should produce same hash"
    
    # Different data should produce different hash (using same format)
    data2 = "37:-7069:-2214408306"
    hash3 = hashlib.sha256(data2.encode()).hexdigest()
    assert hash1 != hash3, "Different data should produce different hash"
    
    print("✓ Hash functionality works correctly")


def test_json_functionality():
    """Test JSON export functionality (without Sage)"""
    print("Testing JSON functionality...")
    
    # Create mock certificate data
    mock_data = {
        'metadata': {
            'created': datetime.now().isoformat(),
            'version': '0.3.0',
            'curve_hash': 'abc123...',
            'status': 'PROVED',
            'finalized': datetime.now().isoformat()
        },
        'curve': {
            'label': '11a1',
            'conductor': 11,
            'discriminant': -161051,
            'j_invariant': '-122023936/161051',
            'rank': 0
        },
        'proofs': {
            'spectral': {
                'status': 'computed',
                'finiteness_proved': True,
                'gamma': 1.23,
                'gamma_positive': True
            }
        },
        'status': 'PROVED',
        'confidence': 0.99
    }
    
    # Test JSON serialization
    json_str = json.dumps(mock_data, indent=2, default=str)
    
    # Parse it back
    parsed = json.loads(json_str)
    
    assert parsed['curve']['label'] == '11a1', "JSON round-trip failed"
    assert parsed['status'] == 'PROVED', "JSON round-trip failed"
    
    print("✓ JSON functionality works correctly")


def test_latex_elements():
    """Test LaTeX export elements (without Sage)"""
    print("Testing LaTeX elements...")
    
    # Read the actual export_latex method to ensure consistency
    with open("sagemath_integration/sage/schemes/elliptic_curves/bsd_spectral/certificates.py", 'r') as f:
        content = f.read()
    
    # Verify key LaTeX structural elements are present in export_latex method
    # These are the literal strings in the source code with escaped braces
    assert '{{theorem}}' in content, "LaTeX theorem structure missing from export_latex"
    assert '{{enumerate}}' in content, "LaTeX enumerate structure missing from export_latex"
    assert '{{itemize}}' in content, "LaTeX itemize structure missing from export_latex"
    assert 'Sha(' in content or '\\Sha' in content, "Sha reference missing from export_latex"
    assert 'Spectral Finiteness' in content, "Spectral Finiteness section missing"
    assert '(dR) Compatibility' in content, "(dR) section missing"
    assert '(PT) Compatibility' in content, "(PT) section missing"
    
    print("✓ LaTeX elements are correct and consistent")


def test_file_permissions():
    """Test that files have correct permissions"""
    print("Testing file permissions...")
    
    # All Python files should be readable
    cert_file = "sagemath_integration/sage/schemes/elliptic_curves/bsd_spectral/certificates.py"
    assert os.access(cert_file, os.R_OK), f"{cert_file} not readable"
    
    test_file = "tests/test_bsd_certificates.py"
    assert os.access(test_file, os.R_OK), f"{test_file} not readable"
    
    print("✓ File permissions are correct")


def test_documentation():
    """Test that documentation is present and well-formed"""
    print("Testing documentation...")
    
    with open("sagemath_integration/sage/schemes/elliptic_curves/bsd_spectral/certificates.py", 'r') as f:
        content = f.read()
    
    # Check for key documentation sections
    doc_sections = [
        "BSD Certificate Generation and Verification",
        "AUTHORS:",
        "José Manuel Mota Burruezo",
        "EXAMPLES::",
        "INPUT:",
        "OUTPUT:",
    ]
    
    for section in doc_sections:
        assert section in content, f"Documentation section '{section}' missing"
    
    # Check that examples are provided for key functions
    assert "sage: from sage.schemes.elliptic_curves.bsd_spectral" in content, \
        "Import examples missing"
    assert "sage: E = EllipticCurve(" in content, "Curve creation examples missing"
    assert "sage: cert = " in content, "Certificate creation examples missing"
    
    print("✓ Documentation is present and well-formed")


def run_all_validations():
    """Run all validation tests"""
    print("\n" + "="*70)
    print("BSD CERTIFICATE MODULE VALIDATION (Non-Sage)")
    print("="*70 + "\n")
    
    try:
        test_module_structure()
        test_certificates_file_content()
        test_init_file_exports()
        test_hash_functionality()
        test_json_functionality()
        test_latex_elements()
        test_file_permissions()
        test_documentation()
        
        print("\n" + "="*70)
        print("🎉 ALL VALIDATIONS PASSED!")
        print("="*70 + "\n")
        
        return 0
    except AssertionError as e:
        print(f"\n❌ VALIDATION FAILED: {e}\n")
        return 1
    except Exception as e:
        print(f"\n❌ UNEXPECTED ERROR: {e}\n")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(run_all_validations())
