"""
Tests for BSD Experimental Validation Module
=============================================

Tests the new_validation module for BSD formula validation
on non-standard elliptic curves.

Author: BSD Spectral Framework
Date: November 2025
"""

import json
import os
import sys
import tempfile

import pytest

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class TestCurveGenerator:
    """Tests for curve_generator module."""
    
    def test_get_experimental_curve_definitions(self):
        """Test that curve definitions are returned correctly."""
        from new_validation.curve_generator import get_experimental_curve_definitions
        
        curves = get_experimental_curve_definitions()
        
        assert isinstance(curves, dict)
        assert len(curves) >= 3  # At least 3 experimental curves
        
        # Check structure of curve definitions
        for label, info in curves.items():
            assert 'coefficients' in info or 'cremona_label' in info
            assert 'description' in info
            assert 'expected_rank' in info
    
    def test_curve_definitions_have_expected_properties(self):
        """Test that curves have expected high conductors or ranks."""
        from new_validation.curve_generator import get_experimental_curve_definitions
        
        curves = get_experimental_curve_definitions()
        
        # At least one curve should have expected_rank >= 2
        high_rank_curves = [c for c in curves.values() if c.get('expected_rank', 0) >= 2]
        assert len(high_rank_curves) >= 1, "Should have at least one high-rank curve"
        
        # Check that E5077b1 is included (famous rank 3 curve)
        assert 'E5077b1' in curves, "E5077b1 should be in experimental curves"


class TestQCALSeal:
    """Tests for QCAL seal module."""
    
    def test_compute_j_invariant_hash(self):
        """Test j-invariant hashing."""
        from new_validation.qcal_seal import compute_j_invariant_hash
        
        # Test with known values
        hash1 = compute_j_invariant_hash("12345/67")
        hash2 = compute_j_invariant_hash("12345/67")
        hash3 = compute_j_invariant_hash("different")
        
        assert len(hash1) == 64  # SHA-256 produces 64 hex chars
        assert hash1 == hash2    # Same input should give same hash
        assert hash1 != hash3    # Different input should give different hash
    
    def test_generate_qcal_seal(self):
        """Test QCAL seal generation."""
        from new_validation.qcal_seal import generate_qcal_seal
        
        # Create mock experiment results
        mock_results = {
            'terms': {
                'j_invariant': '123/456',
                'conductor': 5077,
                'rank': 3,
            },
            'lhs': 1.23e-6,
            'rhs_sha_1': 1.22e-6,
            'sha_estimate': 1.008,
            'relative_error': 0.008,
            'sha_is_1': True,
        }
        
        seal = generate_qcal_seal(mock_results)
        
        assert 'version' in seal
        assert 'timestamp' in seal
        assert 'qcal_frequency_hz' in seal
        assert seal['qcal_frequency_hz'] == 141.7001
        assert 'curve_data' in seal
        assert 'validation' in seal
        assert 'signature' in seal
        
        # Check validation status
        assert seal['validation']['status'] == '✓ experimental match'
    
    def test_verify_qcal_seal(self):
        """Test QCAL seal verification."""
        from new_validation.qcal_seal import generate_qcal_seal, verify_qcal_seal
        
        mock_results = {
            'terms': {
                'j_invariant': '999/1',
                'conductor': 1171,
                'rank': 2,
            },
            'sha_estimate': 0.99,
            'relative_error': 0.01,
        }
        
        seal = generate_qcal_seal(mock_results)
        verification = verify_qcal_seal(seal)
        
        assert verification['valid'] is True
        assert verification['signature_match'] is True
    
    def test_seal_certificate_generation(self):
        """Test seal certificate text generation."""
        from new_validation.qcal_seal import generate_qcal_seal, generate_seal_certificate
        
        mock_results = {
            'terms': {
                'j_invariant': 'test',
                'conductor': 100,
                'rank': 0,
            },
            'sha_estimate': 1.0,
            'relative_error': 0.001,
        }
        
        seal = generate_qcal_seal(mock_results)
        cert = generate_seal_certificate(seal, format='text')
        
        assert 'QCAL SEAL CERTIFICATE' in cert
        assert 'Conductor: 100' in cert
        assert 'Rank: 0' in cert


class TestSummaryGenerator:
    """Tests for summary generator module."""
    
    def test_generate_summary_csv(self):
        """Test CSV summary generation."""
        from new_validation.summary_generator import generate_summary_csv
        
        mock_results = [
            {
                'label': 'test1',
                'comparison': {
                    'terms': {
                        'conductor': 5077,
                        'rank': 3,
                        'j_invariant': '123',
                        'torsion': {'order': 1},
                        'omega': {'omega_plus': 1.5},
                        'regulator': {'value': 2.5},
                        'tamagawa': {'product': 1},
                    },
                    'lhs': 1e-5,
                    'rhs_sha_1': 1e-5,
                    'sha_estimate': 1.0,
                    'relative_error': 0.001,
                    'sha_is_1': True,
                },
            },
        ]
        
        with tempfile.TemporaryDirectory() as tmpdir:
            csv_path = os.path.join(tmpdir, 'test.csv')
            result_path = generate_summary_csv(mock_results, csv_path)
            
            assert os.path.exists(result_path)
            
            with open(result_path) as f:
                content = f.read()
            
            assert 'label' in content
            assert 'test1' in content
            assert '5077' in content
    
    def test_generate_readme_genesis(self):
        """Test README generation."""
        from new_validation.summary_generator import generate_readme_genesis
        
        mock_results = [
            {
                'label': 'E5077b1',
                'comparison': {
                    'terms': {
                        'conductor': 5077,
                        'rank': 3,
                        'j_invariant': '-999/1',
                        'torsion': {'order': 1, 'structure': []},
                        'omega': {'omega_plus': 1.234},
                        'regulator': {'value': 0.456},
                        'tamagawa': {'product': 1},
                    },
                    'lhs': 1.5e-6,
                    'rhs_sha_1': 1.5e-6,
                    'sha_estimate': 1.0,
                    'relative_error': 0.001,
                    'sha_is_1': True,
                },
            },
        ]
        
        with tempfile.TemporaryDirectory() as tmpdir:
            readme_path = os.path.join(tmpdir, 'README.md')
            result_path = generate_readme_genesis(mock_results, readme_path)
            
            assert os.path.exists(result_path)
            
            with open(result_path) as f:
                content = f.read()
            
            assert 'BSD Genesis' in content or 'BSD' in content
            assert 'E5077b1' in content
            assert '5077' in content
            assert 'QCAL' in content


class TestModuleImports:
    """Test that all module imports work correctly."""
    
    def test_import_curve_generator(self):
        """Test curve_generator imports."""
        from new_validation.curve_generator import (
            get_experimental_curve_definitions,
            generate_experimental_curves,
            get_curve_invariants,
            validate_curve_selection,
        )
        
        assert callable(get_experimental_curve_definitions)
        assert callable(generate_experimental_curves)
    
    def test_import_qcal_seal(self):
        """Test qcal_seal imports."""
        from new_validation.qcal_seal import (
            generate_qcal_seal,
            verify_qcal_seal,
            compute_j_invariant_hash,
            generate_seal_certificate,
        )
        
        assert callable(generate_qcal_seal)
        assert callable(verify_qcal_seal)
    
    def test_import_summary_generator(self):
        """Test summary_generator imports."""
        from new_validation.summary_generator import (
            generate_summary_csv,
            generate_readme_genesis,
            generate_all_summaries,
        )
        
        assert callable(generate_summary_csv)
        assert callable(generate_readme_genesis)


class TestBSDExperimentUnit:
    """Unit tests for BSD experiment module (without SageMath)."""
    
    def test_bsd_experiment_module_imports(self):
        """Test that bsd_experiment module can be imported."""
        # This should work even without sage
        from new_validation import bsd_experiment
        
        assert hasattr(bsd_experiment, 'BSDExperiment')
        assert hasattr(bsd_experiment, 'compute_bsd_comparison')
        assert hasattr(bsd_experiment, 'generate_curve_json')
        assert hasattr(bsd_experiment, 'run_bsd_experiment')


@pytest.mark.skipif(
    not os.environ.get('SAGE_AVAILABLE'),
    reason="SageMath not available"
)
class TestBSDExperimentWithSage:
    """Integration tests requiring SageMath."""
    
    def test_bsd_experiment_11a1(self):
        """Test BSD experiment on 11a1 (simplest curve)."""
        from sage.all import EllipticCurve
        from new_validation.bsd_experiment import BSDExperiment
        
        E = EllipticCurve('11a1')
        experiment = BSDExperiment(E, '11a1')
        
        comparison = experiment.compute_bsd_comparison()
        
        assert 'terms' in comparison
        assert comparison['terms']['conductor'] == 11
        assert comparison['terms']['rank'] == 0
        
        # For 11a1, Sha = 1 is known
        assert comparison.get('sha_estimate') is not None
    
    def test_bsd_experiment_37a1(self):
        """Test BSD experiment on 37a1 (rank 1)."""
        from sage.all import EllipticCurve
        from new_validation.bsd_experiment import BSDExperiment
        
        E = EllipticCurve('37a1')
        experiment = BSDExperiment(E, '37a1')
        
        comparison = experiment.compute_bsd_comparison()
        
        assert comparison['terms']['conductor'] == 37
        assert comparison['terms']['rank'] == 1
    
    def test_run_bsd_experiment_creates_files(self):
        """Test that run_bsd_experiment creates output files."""
        from sage.all import EllipticCurve
        from new_validation.bsd_experiment import run_bsd_experiment
        
        E = EllipticCurve('11a1')
        
        with tempfile.TemporaryDirectory() as tmpdir:
            output_dir = os.path.join(tmpdir, 'E11a1')
            result = run_bsd_experiment(E, '11a1', output_dir)
            
            assert os.path.exists(os.path.join(output_dir, 'curve.json'))
            assert os.path.exists(os.path.join(output_dir, 'output.txt'))
            assert os.path.exists(os.path.join(output_dir, 'bsd_results.json'))


def run_all_tests():
    """Run all tests manually."""
    print("Running BSD Experimental Validation Tests...")
    print("=" * 60)
    
    # Run tests that don't require sage
    test_classes = [
        TestCurveGenerator,
        TestQCALSeal,
        TestSummaryGenerator,
        TestModuleImports,
        TestBSDExperimentUnit,
    ]
    
    for test_class in test_classes:
        print(f"\n{test_class.__name__}:")
        instance = test_class()
        for method_name in dir(instance):
            if method_name.startswith('test_'):
                try:
                    getattr(instance, method_name)()
                    print(f"  ✓ {method_name}")
                except Exception as e:
                    print(f"  ✗ {method_name}: {e}")
    
    print("\n" + "=" * 60)
    print("Tests completed!")


if __name__ == '__main__':
    run_all_tests()
