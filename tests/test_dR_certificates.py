"""
Tests for dR uniformity certificate generation
"""

import sys
import os
import json
import pytest

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))


def test_validation_data_exists():
    """Test that validation data JSON file exists and is valid"""
    data_path = "validation_dR_uniformity_results.json"
    assert os.path.exists(data_path), f"Data file not found: {data_path}"
    
    with open(data_path, 'r') as f:
        data = json.load(f)
    
    # Check metadata
    assert 'metadata' in data
    assert 'results' in data
    assert 'summary' in data
    
    # Check metadata fields
    metadata = data['metadata']
    assert metadata['title'] == "Fontaine-Perrin-Riou (dR) Compatibility Validation"
    assert metadata['institution'] == "Instituto Conciencia Cuántica (ICQ)"
    
    # Check results
    results = data['results']
    assert len(results) == 20, f"Expected 20 curves, got {len(results)}"
    
    # Check summary
    summary = data['summary']
    assert summary['total_curves'] == 20
    assert summary['passed'] == 18
    assert summary['failed'] == 2
    assert summary['success_rate'] == 0.90
    
    print("✓ Validation data JSON is valid")


def test_latex_template_exists():
    """Test that LaTeX template exists"""
    template_path = "certificados/template_certificate_dR.tex"
    assert os.path.exists(template_path), f"Template not found: {template_path}"
    
    with open(template_path, 'r') as f:
        content = f.read()
    
    # Check for required placeholders
    assert '\\VARcurve' in content
    assert '\\VARpentries' in content
    assert '\\VARconclusion' in content
    
    # Check for required LaTeX commands
    assert '\\OK' in content
    assert '\\FAIL' in content
    assert 'Instituto Conciencia Cuántica' in content
    assert 'Fontaine–Perrin–Riou' in content
    
    print("✓ LaTeX template is valid")


def test_generator_script_exists():
    """Test that generator script exists and is executable"""
    script_path = "scripts/generate_dR_certificates.py"
    assert os.path.exists(script_path), f"Script not found: {script_path}"
    
    with open(script_path, 'r') as f:
        content = f.read()
    
    # Check for required functions
    assert 'generate_dR_certificates' in content
    assert 'TEMPLATE_PATH' in content
    assert 'DATA_PATH' in content
    
    print("✓ Generator script exists")


def test_certificate_generation():
    """Test that certificates can be generated"""
    # Import and run the generator
    from scripts.generate_dR_certificates import generate_dR_certificates
    
    # Run generation
    generate_dR_certificates()
    
    # Check that certificates were created
    cert_dir = "certificados/"
    tex_files = [f for f in os.listdir(cert_dir) if f.startswith('certificate_dR_uniformity_') and f.endswith('.tex')]
    
    assert len(tex_files) == 20, f"Expected 20 certificates, found {len(tex_files)}"
    
    print(f"✓ Generated {len(tex_files)} certificates")


def test_certificate_content():
    """Test that generated certificates have correct content"""
    # Test a passing certificate
    cert_path = "certificados/certificate_dR_uniformity_11a1.tex"
    assert os.path.exists(cert_path), f"Certificate not found: {cert_path}"
    
    with open(cert_path, 'r') as f:
        content = f.read()
    
    # Check curve label
    assert "EllipticCurve('11a1')" in content
    
    # Check for results table
    assert '\\toprule' in content
    assert '\\midrule' in content
    assert '\\bottomrule' in content
    assert '\\OK' in content
    
    # Check for passing conclusion
    assert 'Compatibilidad dR confirmada' in content or '✅' in content
    
    print("✓ Certificate content is correct for 11a1")


def test_failing_certificate_content():
    """Test that failing certificates have correct warning content"""
    # Test a failing certificate
    cert_path = "certificados/certificate_dR_uniformity_32a1.tex"
    assert os.path.exists(cert_path), f"Certificate not found: {cert_path}"
    
    with open(cert_path, 'r') as f:
        content = f.read()
    
    # Check curve label
    assert "EllipticCurve('32a1')" in content
    
    # Check for failure markers
    assert '\\FAIL' in content
    
    # Check for warning conclusion
    assert 'desviaciones' in content or '⚠️' in content or 'reducción aditiva' in content
    
    print("✓ Certificate content is correct for 32a1 (expected failure)")


def test_documentation_exists():
    """Test that documentation file exists"""
    doc_path = "VALIDATION_dR_UNIFORMITY.md"
    assert os.path.exists(doc_path), f"Documentation not found: {doc_path}"
    
    with open(doc_path, 'r') as f:
        content = f.read()
    
    # Check for required sections
    assert 'Fontaine–Perrin–Riou' in content or 'Fontaine-Perrin-Riou' in content
    assert 'Uso' in content or 'Usage' in content
    assert 'generate_dR_certificates.py' in content
    assert 'validation_dR_uniformity_results.json' in content
    
    print("✓ Documentation is complete")


if __name__ == "__main__":
    # Run tests manually
    test_validation_data_exists()
    test_latex_template_exists()
    test_generator_script_exists()
    test_certificate_generation()
    test_certificate_content()
    test_failing_certificate_content()
    test_documentation_exists()
    print("\n✅ All tests passed!")
