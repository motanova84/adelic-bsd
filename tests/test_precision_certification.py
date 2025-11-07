"""
Tests for Precision Certification Module

Validates the numerical precision certification functionality.
"""

import pytest
import sys
import os
import numpy as np

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from src.precision_certification import (
    PrecisionCertificate,
    PrecisionVerifier,
    certify_computation
)


@pytest.mark.basic
def test_certificate_initialization():
    """Test precision certificate initialization."""
    cert = PrecisionCertificate('test_computation')
    
    assert cert.computation_id == 'test_computation'
    assert cert.status == 'unverified'
    assert len(cert.precision_tests) == 0
    assert len(cert.error_bounds) == 0


@pytest.mark.basic
def test_certificate_add_test():
    """Test adding precision test to certificate."""
    cert = PrecisionCertificate('test_computation')
    
    test_result = {'passed': True, 'error': 1e-12}
    cert.add_precision_test('test_determinant', test_result)
    
    assert len(cert.precision_tests) == 1
    assert cert.precision_tests[0]['test'] == 'test_determinant'
    assert cert.precision_tests[0]['result']['passed'] is True


@pytest.mark.basic
def test_certificate_set_error_bound():
    """Test setting error bounds in certificate."""
    cert = PrecisionCertificate('test_computation')
    
    cert.set_error_bound('determinant', 1e-10, 'relative')
    cert.set_error_bound('eigenvalue', 1e-12, 'absolute')
    
    assert len(cert.error_bounds) == 2
    assert cert.error_bounds['determinant']['bound'] == 1e-10
    assert cert.error_bounds['determinant']['unit'] == 'relative'


@pytest.mark.basic
def test_certificate_certify_pass():
    """Test certificate certification with passing tests."""
    cert = PrecisionCertificate('test_computation')
    
    cert.add_precision_test('test1', {'passed': True})
    cert.add_precision_test('test2', {'passed': True})
    
    result = cert.certify()
    
    assert result is True
    assert cert.status == 'certified'


@pytest.mark.basic
def test_certificate_certify_fail():
    """Test certificate certification with failing tests."""
    cert = PrecisionCertificate('test_computation')
    
    cert.add_precision_test('test1', {'passed': True})
    cert.add_precision_test('test2', {'passed': False})
    
    result = cert.certify()
    
    assert result is False
    assert cert.status == 'failed'


@pytest.mark.basic
def test_certificate_to_dict():
    """Test certificate export to dictionary."""
    cert = PrecisionCertificate('test_computation')
    cert.add_precision_test('test1', {'passed': True})
    cert.set_error_bound('determinant', 1e-10)
    cert.certify()
    
    data = cert.to_dict()
    
    assert isinstance(data, dict)
    assert data['computation_id'] == 'test_computation'
    assert data['status'] == 'certified'
    assert len(data['precision_tests']) == 1
    assert len(data['error_bounds']) == 1


@pytest.mark.basic
def test_certificate_save(tmp_path):
    """Test saving certificate to file."""
    cert = PrecisionCertificate('test_computation')
    cert.add_precision_test('test1', {'passed': True})
    cert.certify()
    
    output_file = tmp_path / "cert.json"
    cert.save(output_file)
    
    assert output_file.exists()
    
    # Verify file content
    import json
    with output_file.open() as f:
        data = json.load(f)
    
    assert data['computation_id'] == 'test_computation'


@pytest.mark.basic
def test_verifier_initialization():
    """Test precision verifier initialization."""
    verifier = PrecisionVerifier(tolerance=1e-8)
    
    assert verifier.tolerance == 1e-8
    assert len(verifier.certificates) == 0


@pytest.mark.basic
def test_verify_matrix_determinant_2x2():
    """Test determinant verification for 2x2 matrix."""
    verifier = PrecisionVerifier()
    
    matrix = np.array([[1.0, 2.0], [3.0, 4.0]])
    # det = 1*4 - 2*3 = -2
    
    result = verifier.verify_matrix_determinant(matrix, expected=-2.0)
    
    assert result['passed'] is True
    assert abs(result['det_numpy'] - (-2.0)) < 1e-10
    assert 'det_cofactor' in result


@pytest.mark.basic
def test_verify_matrix_determinant_3x3():
    """Test determinant verification for 3x3 matrix."""
    verifier = PrecisionVerifier()
    
    matrix = np.array([
        [1.0, 0.0, 0.0],
        [0.0, 2.0, 0.0],
        [0.0, 0.0, 3.0]
    ])
    # det = 1*2*3 = 6
    
    result = verifier.verify_matrix_determinant(matrix, expected=6.0)
    
    assert result['passed'] is True
    assert abs(result['det_numpy'] - 6.0) < 1e-10


@pytest.mark.basic
def test_verify_eigenvalues():
    """Test eigenvalue verification."""
    verifier = PrecisionVerifier()
    
    # Diagonal matrix - eigenvalues are diagonal elements
    matrix = np.array([
        [1.0, 0.0],
        [0.0, 2.0]
    ])
    
    result = verifier.verify_eigenvalues(matrix)
    
    assert result['passed'] is True
    assert abs(result['trace'] - 3.0) < 1e-10  # trace = 1 + 2 = 3
    assert abs(result['det'] - 2.0) < 1e-10    # det = 1 * 2 = 2


@pytest.mark.basic
def test_verify_eigenvalues_symmetric():
    """Test eigenvalue verification for symmetric matrix."""
    verifier = PrecisionVerifier()
    
    # Symmetric matrix with known eigenvalues
    matrix = np.array([
        [2.0, 1.0],
        [1.0, 2.0]
    ])
    # eigenvalues: 3, 1
    
    result = verifier.verify_eigenvalues(matrix)
    
    assert result['passed'] is True
    assert abs(result['trace'] - 4.0) < 1e-10  # trace = 2 + 2 = 4
    assert abs(result['det'] - 3.0) < 1e-10    # det = 2*2 - 1*1 = 3


@pytest.mark.basic
def test_verify_numerical_stability_monotonic():
    """Test verification of monotonic sequence."""
    verifier = PrecisionVerifier()
    
    values = [1.0, 2.0, 3.0, 4.0, 5.0]
    result = verifier.verify_numerical_stability(values, 'monotonic')
    
    assert result['passed'] is True
    assert result['monotonic_increasing'] is True


@pytest.mark.basic
def test_verify_numerical_stability_bounded():
    """Test verification of bounded sequence."""
    verifier = PrecisionVerifier()
    
    values = [1.0, 2.0, 1.5, 2.5, 1.8]
    result = verifier.verify_numerical_stability(values, 'bounded')
    
    assert result['passed'] is True
    assert result['bounded'] is True


@pytest.mark.basic
def test_verify_numerical_stability_convergent():
    """Test verification of convergent sequence."""
    verifier = PrecisionVerifier(tolerance=1e-6)
    
    # Sequence that's already converged (all same values at the end)
    values = [2.0, 1.5, 1.2, 1.1, 1.05, 1.02, 1.01, 1.005, 1.002, 1.001] + [1.0] * 5
    result = verifier.verify_numerical_stability(values, 'convergent', tolerance=0.02)
    
    # Should pass because the last 10 values have differences < 0.02
    assert result['passed'] is True
    assert result.get('convergent', False) is True


@pytest.mark.basic
def test_verify_spectral_operator():
    """Test verification of spectral operator data."""
    verifier = PrecisionVerifier()
    
    operator_data = {
        'local_data': {
            2: {
                'operator': [[1.0, 0.0], [0.0, 2.0]]
            },
            3: {
                'operator': [[2.0, 1.0], [1.0, 2.0]]
            }
        }
    }
    
    result = verifier.verify_spectral_operator(operator_data)
    
    assert 'passed' in result
    assert 'detailed_results' in result


@pytest.mark.basic
def test_create_certificate():
    """Test creating precision certificate."""
    verifier = PrecisionVerifier()
    
    spectral_data = {
        'local_data': {
            2: {
                'operator': [[1.0, 0.0], [0.0, 1.0]]
            }
        }
    }
    
    cert = verifier.create_certificate('test_comp', spectral_data)
    
    assert isinstance(cert, PrecisionCertificate)
    assert cert.computation_id == 'test_comp'
    assert len(cert.precision_tests) > 0


@pytest.mark.basic
def test_generate_precision_report():
    """Test generating precision report."""
    verifier = PrecisionVerifier()
    
    spectral_data = {
        'local_data': {
            2: {
                'operator': [[1.0, 0.0], [0.0, 1.0]]
            }
        }
    }
    
    cert = verifier.create_certificate('test_comp', spectral_data)
    report = verifier.generate_precision_report()
    
    assert isinstance(report, str)
    assert 'PRECISION CERTIFICATION REPORT' in report
    assert 'test_comp' in report


@pytest.mark.basic
def test_certify_computation(tmp_path):
    """Test complete certification workflow."""
    spectral_data = {
        'local_data': {
            2: {
                'operator': [[1.0, 0.0], [0.0, 1.0]]
            }
        }
    }
    
    cert = certify_computation('test_comp', spectral_data, 
                              tolerance=1e-10, output_dir=tmp_path)
    
    assert isinstance(cert, PrecisionCertificate)
    
    # Check that files were created
    cert_file = tmp_path / 'precision_cert_test_comp.json'
    report_file = tmp_path / 'precision_report.txt'
    
    assert cert_file.exists()
    assert report_file.exists()


@pytest.mark.basic
def test_determinant_cofactor_method():
    """Test cofactor determinant computation."""
    verifier = PrecisionVerifier()
    
    # 1x1 matrix
    det = verifier._determinant_cofactor(np.array([[5.0]]))
    assert abs(det - 5.0) < 1e-10
    
    # 2x2 matrix
    det = verifier._determinant_cofactor(np.array([[1.0, 2.0], [3.0, 4.0]]))
    assert abs(det - (-2.0)) < 1e-10
    
    # 3x3 matrix
    det = verifier._determinant_cofactor(np.array([
        [1.0, 0.0, 0.0],
        [0.0, 2.0, 0.0],
        [0.0, 0.0, 3.0]
    ]))
    assert abs(det - 6.0) < 1e-10


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
