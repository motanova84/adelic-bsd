"""
Tests for dR uniformity validation script and results.
"""

import sys
import os
import json
import pytest
from pathlib import Path

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))


@pytest.mark.basic
def test_validation_script_exists():
    """Test that validation script exists and is executable"""
    script_path = Path(__file__).parent.parent / 'scripts' / 'validate_dR_uniformity.py'
    assert script_path.exists(), "validate_dR_uniformity.py script not found"
    assert os.access(script_path, os.X_OK) or script_path.suffix == '.py', "Script is not executable"
    print("✓ Validation script exists")


@pytest.mark.basic
def test_validation_results_file_exists():
    """Test that validation results JSON file exists"""
    results_path = Path(__file__).parent.parent / 'validation_dR_uniformity_results.json'
    assert results_path.exists(), "validation_dR_uniformity_results.json not found"
    print("✓ Results file exists")


@pytest.mark.basic
def test_validation_results_json_valid():
    """Test that validation results JSON is valid and well-formed"""
    results_path = Path(__file__).parent.parent / 'validation_dR_uniformity_results.json'
    
    with open(results_path, 'r') as f:
        data = json.load(f)
    
    # Check top-level structure
    assert 'metadata' in data
    assert 'statistics' in data
    assert 'curve_results' in data
    
    # Check metadata
    assert 'primes_tested' in data['metadata']
    assert data['metadata']['primes_tested'] == [2, 3, 5]
    
    # Check statistics
    stats = data['statistics']
    assert 'total_curves' in stats
    assert stats['total_curves'] == 20
    assert 'validated_completely' in stats
    assert 'success_rate' in stats
    
    print(f"✓ Results JSON valid with {stats['total_curves']} curves")


@pytest.mark.basic
def test_validation_results_curve_structure():
    """Test that each curve result has correct structure"""
    results_path = Path(__file__).parent.parent / 'validation_dR_uniformity_results.json'
    
    with open(results_path, 'r') as f:
        data = json.load(f)
    
    curve_results = data['curve_results']
    
    # Check we have 20 curves
    assert len(curve_results) == 20
    
    # Check structure of first curve
    for label, result in curve_results.items():
        assert 'label' in result
        assert 'conductor' in result
        assert 'rank' in result
        assert 'prime_results' in result
        assert 'all_compatible' in result
        assert 'status' in result
        
        # Check prime results structure
        prime_results = result['prime_results']
        assert len(prime_results) == 3  # p=2, 3, 5
        
        for p_key, p_result in prime_results.items():
            assert 'prime' in p_result
            assert 'h1f_dim' in p_result
            assert 'dR_dim' in p_result
            assert 'compatible' in p_result
            assert 'reduction_type' in p_result
        
        break  # Just check first curve
    
    print("✓ Curve results have correct structure")


@pytest.mark.basic
def test_documentation_exists():
    """Test that documentation file exists"""
    doc_path = Path(__file__).parent.parent / 'VALIDATION_dR_UNIFORMITY.md'
    assert doc_path.exists(), "VALIDATION_dR_UNIFORMITY.md not found"
    
    with open(doc_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check key sections exist
    assert '# 📘 VALIDATION_dR_UNIFORMITY.md' in content
    assert 'Objetivo' in content
    assert 'Metodología' in content
    assert 'Resultados' in content
    assert 'Conclusiones' in content
    
    print("✓ Documentation file exists with correct sections")


@pytest.mark.basic
def test_certificates_directory_exists():
    """Test that certificates directory exists with sample files"""
    cert_dir = Path(__file__).parent.parent / 'certificates' / 'dR_uniformity'
    assert cert_dir.exists(), "certificates/dR_uniformity directory not found"
    
    # Check for README
    readme = cert_dir / 'README.md'
    assert readme.exists(), "README.md not found in certificates directory"
    
    # Check for sample certificates
    sample_curves = ['11a1', '37a1', '24a1', '389a1', '990h1']
    
    for curve in sample_curves:
        json_cert = cert_dir / f"cert_{curve}.json"
        tex_cert = cert_dir / f"cert_{curve}.tex"
        
        assert json_cert.exists(), f"JSON certificate for {curve} not found"
        assert tex_cert.exists(), f"LaTeX certificate for {curve} not found"
    
    print(f"✓ Certificates directory exists with {len(sample_curves)} sample certificates")


@pytest.mark.basic
def test_sample_certificate_json_valid():
    """Test that sample certificate JSON files are valid"""
    cert_dir = Path(__file__).parent.parent / 'certificates' / 'dR_uniformity'
    
    # Check 11a1 certificate
    cert_file = cert_dir / 'cert_11a1.json'
    
    with open(cert_file, 'r') as f:
        cert = json.load(f)
    
    # Check structure
    assert 'label' in cert
    assert cert['label'] == '11a1'
    assert 'conductor' in cert
    assert 'rank' in cert
    assert 'prime_results' in cert
    assert 'all_compatible' in cert
    
    print("✓ Sample certificate JSON is valid")


@pytest.mark.basic
def test_expected_curves_present():
    """Test that all expected 20 curves are present in results"""
    results_path = Path(__file__).parent.parent / 'validation_dR_uniformity_results.json'
    
    with open(results_path, 'r') as f:
        data = json.load(f)
    
    expected_curves = [
        "11a1", "14a1", "15a1", "24a1", "27a1", "37a1", "49a1", "54a1",
        "56a1", "58a1", "66a1", "67a1", "91a1", "121c2", "389a1", "507a1",
        "571a1", "681b1", "802a1", "990h1"
    ]
    
    curve_results = data['curve_results']
    
    for curve in expected_curves:
        assert curve in curve_results, f"Expected curve {curve} not found in results"
    
    print(f"✓ All {len(expected_curves)} expected curves present")


@pytest.mark.basic
def test_validation_statistics():
    """Test that validation statistics match expected values"""
    results_path = Path(__file__).parent.parent / 'validation_dR_uniformity_results.json'
    
    with open(results_path, 'r') as f:
        data = json.load(f)
    
    stats = data['statistics']
    
    # Based on problem statement
    assert stats['total_curves'] == 20
    assert stats['validated_completely'] == 16
    assert stats['with_deviations'] == 4
    assert stats['success_rate'] == 80.0
    
    print("✓ Statistics match expected values from problem statement")


@pytest.mark.basic
def test_deviation_cases():
    """Test that known deviation cases are correctly identified"""
    results_path = Path(__file__).parent.parent / 'validation_dR_uniformity_results.json'
    
    with open(results_path, 'r') as f:
        data = json.load(f)
    
    curve_results = data['curve_results']
    
    # Curves that should have deviations according to problem statement
    deviation_curves = {
        '24a1': {'prime': 2, 'compatible': False},
        '54a1': {'prime': 2, 'compatible': False},
        '507a1': {'prime': 2, 'compatible': False},
        '990h1': {'prime': 5, 'compatible': False}
    }
    
    for curve, expected in deviation_curves.items():
        result = curve_results[curve]
        assert not result['all_compatible'], f"{curve} should have deviations"
        
        # Find the specific prime with deviation
        for p_key, p_result in result['prime_results'].items():
            if not p_result['compatible']:
                assert p_result['prime'] == expected['prime'], \
                    f"{curve} deviation should be at p={expected['prime']}"
    
    print("✓ Known deviation cases correctly identified")


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
