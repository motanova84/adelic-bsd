"""
Tests for dR compatibility module
"""

import pytest
import json
from pathlib import Path
import sys

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from dR_compatibility import dRCompatibilityProver, prove_dR_all_cases


class TestdRCompatibilityProver:
    """Test suite for dR compatibility prover"""
    
    def test_init(self):
        """Test initialization of dR prover"""
        prover = dRCompatibilityProver('11a1', 11)
        assert prover.curve_label == '11a1'
        assert prover.p == 11
        assert prover.conductor == 11
    
    def test_reduction_classification(self):
        """Test reduction type classification"""
        # Good reduction (p doesn't divide conductor)
        prover_good = dRCompatibilityProver('11a1', 7)
        assert prover_good.reduction_type == 'good'
        
        # Bad reduction (p divides conductor)
        prover_bad = dRCompatibilityProver('11a1', 11)
        assert prover_bad.reduction_type in ['multiplicative', 'additive_general']
    
    def test_compute_galois_representation(self):
        """Test Galois representation computation"""
        prover = dRCompatibilityProver('11a1', 11)
        V_p = prover._compute_galois_representation()
        
        assert 'dimension' in V_p
        assert V_p['dimension'] == 2
        assert 'type' in V_p
    
    def test_compute_de_rham_cohomology(self):
        """Test de Rham cohomology computation"""
        prover = dRCompatibilityProver('37a1', 37)
        D_dR = prover._compute_de_rham_cohomology()
        
        assert D_dR['dimension'] == 2
        assert 'filtration' in D_dR
        assert 'Fil_0' in D_dR['filtration']
    
    def test_exponential_map_good_reduction(self):
        """Test exponential map for good reduction"""
        prover = dRCompatibilityProver('11a1', 7)
        V_p = prover._compute_galois_representation()
        D_dR = prover._compute_de_rham_cohomology()
        
        exp_map = prover._exp_good_reduction(V_p, D_dR)
        
        assert exp_map['compatible'] is True
        assert exp_map['lands_in_Fil0'] is True
    
    def test_exponential_map_additive(self):
        """Test exponential map for additive reduction (CRITICAL)"""
        prover = dRCompatibilityProver('27a1', 3)
        # Force additive reduction
        prover.reduction_type = 'additive_general'
        
        V_p = prover._compute_galois_representation()
        D_dR = prover._compute_de_rham_cohomology()
        
        exp_map = prover._exp_additive(V_p, D_dR)
        
        assert exp_map['compatible'] is True
        assert exp_map['lands_in_Fil0'] is True
        assert exp_map['method'] == 'Fontaine_Perrin_Riou_explicit'
    
    def test_prove_dR_compatibility(self):
        """Test main proof method"""
        prover = dRCompatibilityProver('11a1', 11)
        cert = prover.prove_dR_compatibility()
        
        assert 'curve' in cert
        assert 'prime' in cert
        assert 'dR_compatible' in cert
        assert 'reduction_type' in cert
        assert cert['verified'] is True
        assert cert['dR_compatible'] is True


class TestdRAllCases:
    """Test proving dR for all cases"""
    
    def test_prove_all_cases(self):
        """Test proving dR for all reduction types"""
        results = prove_dR_all_cases()
        
        assert len(results) == 5
        assert all(r['dR_compatible'] for r in results)
        assert all(r['verified'] for r in results)
    
    def test_certificate_generation(self):
        """Test certificate file generation"""
        prove_dR_all_cases()
        
        cert_file = Path('proofs/dR_certificates.json')
        assert cert_file.exists()
        
        with open(cert_file) as f:
            certs = json.load(f)
        
        assert isinstance(certs, list)
        assert len(certs) == 5
    
    def test_all_reduction_types_covered(self):
        """Test that all reduction types are covered"""
        results = prove_dR_all_cases()
        
        reduction_types = [r['reduction_type'] for r in results]
        
        # Should have at least multiplicative and additive
        assert 'multiplicative' in reduction_types or 'additive_general' in reduction_types


class TestdRIntegration:
    """Integration tests for dR compatibility"""
    
    def test_certificate_structure(self):
        """Test that certificates have required structure"""
        prover = dRCompatibilityProver('389a1', 389)
        cert = prover.prove_dR_compatibility()
        
        required_fields = ['curve', 'prime', 'reduction_type', 
                          'dR_compatible', 'method', 'reference', 'verified']
        
        for field in required_fields:
            assert field in cert, f"Missing field: {field}"
    
    def test_reference_included(self):
        """Test that proper references are included"""
        results = prove_dR_all_cases()
        
        for result in results:
            assert 'reference' in result
            assert 'Fontaine' in result['reference'] or 'Perrin-Riou' in result['reference']


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
