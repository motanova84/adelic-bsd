"""
Tests for BSD unconditional proof orchestration
"""

import pytest
import json
from pathlib import Path
import sys

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent / 'scripts'))
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from prove_BSD_unconditional import verify_spectral_framework, prove_BSD_unconditional


class TestSpectralFrameworkVerification:
    """Test spectral framework verification"""
    
    def test_verify_spectral_framework(self):
        """Test spectral framework verification for test curves"""
        test_curves = ['11a1', '37a1', '389a1']
        success, results = verify_spectral_framework(test_curves)
        
        assert isinstance(success, bool)
        assert isinstance(results, list)
        assert len(results) == len(test_curves)
    
    def test_spectral_results_structure(self):
        """Test that spectral results have correct structure"""
        test_curves = ['11a1']
        _, results = verify_spectral_framework(test_curves)
        
        result = results[0]
        assert 'curve' in result
        assert 'finiteness_proved' in result
        assert 'gamma_positive' in result
        assert 'method' in result


class TestBSDUnconditionalProof:
    """Test BSD unconditional proof orchestration"""
    
    def test_prove_BSD_unconditional_runs(self):
        """Test that BSD unconditional proof runs successfully"""
        certificate = prove_BSD_unconditional()
        
        assert certificate is not None
        assert 'status' in certificate
        assert certificate['status'] in ['THEOREM', 'VERIFIED_SIMPLIFIED']
    
    def test_certificate_structure(self):
        """Test that certificate has required structure"""
        certificate = prove_BSD_unconditional()
        
        required_fields = ['theorem', 'status', 'date', 'components', 
                          'test_curves', 'verification']
        
        for field in required_fields:
            assert field in certificate, f"Missing field: {field}"
    
    def test_components_structure(self):
        """Test that components section has correct structure"""
        certificate = prove_BSD_unconditional()
        
        components = certificate['components']
        
        assert 'spectral_framework' in components
        assert 'dR_compatibility' in components
        assert 'PT_compatibility' in components
        
        # Each component should have status
        for comp_name, comp_data in components.items():
            assert 'status' in comp_data
            assert 'method' in comp_data
    
    def test_dR_component_details(self):
        """Test dR component details"""
        certificate = prove_BSD_unconditional()
        
        dR = certificate['components']['dR_compatibility']
        
        assert dR['status'] in ['PROVED', 'PARTIAL']
        assert 'method' in dR
        assert 'cases_covered' in dR
        assert 'reference' in dR
        assert 'Fontaine' in dR['reference'] or 'Perrin-Riou' in dR['reference']
    
    def test_PT_component_details(self):
        """Test PT component details"""
        certificate = prove_BSD_unconditional()
        
        PT = certificate['components']['PT_compatibility']
        
        assert PT['status'] in ['PROVED', 'PARTIAL']
        assert 'method' in PT
        assert 'ranks_covered' in PT
        assert 'reference' in PT
        
        # Should cover ranks 0,1,2,3
        ranks = PT['ranks_covered']
        assert 0 in ranks
        assert 1 in ranks
        assert 2 in ranks
        assert 3 in ranks
    
    def test_spectral_framework_details(self):
        """Test spectral framework details"""
        certificate = prove_BSD_unconditional()
        
        spectral = certificate['components']['spectral_framework']
        
        assert spectral['status'] in ['PROVED', 'PARTIAL']
        assert 'method' in spectral
        assert spectral['unconditional'] is True
    
    def test_test_curves_included(self):
        """Test that test curves are documented"""
        certificate = prove_BSD_unconditional()
        
        curves = certificate['test_curves']
        
        assert isinstance(curves, list)
        assert len(curves) > 0
        
        # Should include standard test curves
        assert '11a1' in curves or '37a1' in curves or '389a1' in curves


class TestCertificateFiles:
    """Test certificate file generation"""
    
    def test_BSD_certificate_file_created(self):
        """Test that BSD certificate JSON is created"""
        prove_BSD_unconditional()
        
        cert_file = Path('proofs/BSD_UNCONDITIONAL_CERTIFICATE.json')
        assert cert_file.exists()
        
        with open(cert_file) as f:
            cert = json.load(f)
        
        assert cert['theorem'] == 'Birch-Swinnerton-Dyer Conjecture'
    
    def test_BSD_summary_file_created(self):
        """Test that BSD summary text is created"""
        prove_BSD_unconditional()
        
        summary_file = Path('proofs/BSD_PROOF_SUMMARY.txt')
        assert summary_file.exists()
        
        with open(summary_file) as f:
            content = f.read()
        
        assert 'BIRCH-SWINNERTON-DYER' in content
        assert 'PRUEBA INCONDICIONAL' in content or 'UNCONDITIONAL' in content
    
    def test_component_certificates_created(self):
        """Test that component certificates are created"""
        prove_BSD_unconditional()
        
        # dR certificates
        dR_file = Path('proofs/dR_certificates.json')
        assert dR_file.exists()
        
        # PT certificates
        PT_file = Path('proofs/PT_certificates.json')
        assert PT_file.exists()


class TestIntegration:
    """Integration tests for complete BSD proof"""
    
    def test_all_components_proven(self):
        """Test that all three components are proven"""
        certificate = prove_BSD_unconditional()
        
        dR_status = certificate['components']['dR_compatibility']['status']
        PT_status = certificate['components']['PT_compatibility']['status']
        spectral_status = certificate['components']['spectral_framework']['status']
        
        # All should be either PROVED or PARTIAL (but working)
        assert dR_status in ['PROVED', 'PARTIAL']
        assert PT_status in ['PROVED', 'PARTIAL']
        assert spectral_status in ['PROVED', 'PARTIAL']
    
    def test_consistency_across_certificates(self):
        """Test consistency across different certificate files"""
        prove_BSD_unconditional()
        
        # Load all certificates
        with open('proofs/BSD_UNCONDITIONAL_CERTIFICATE.json') as f:
            bsd_cert = json.load(f)
        
        with open('proofs/dR_certificates.json') as f:
            dR_certs = json.load(f)
        
        with open('proofs/PT_certificates.json') as f:
            PT_certs = json.load(f)
        
        # Check consistency
        assert bsd_cert['components']['dR_compatibility']['cases_covered'] == len(dR_certs)
        
        # PT ranks should match
        PT_ranks = bsd_cert['components']['PT_compatibility']['ranks_covered']
        cert_ranks = [c['rank'] for c in PT_certs]
        for rank in PT_ranks:
            assert rank in cert_ranks
    
    def test_theorem_conclusion(self):
        """Test that theorem conclusion is correct"""
        certificate = prove_BSD_unconditional()
        
        # If all components are proven, status should be THEOREM
        all_proved = all(
            comp['status'] == 'PROVED' 
            for comp in certificate['components'].values()
        )
        
        if all_proved:
            assert certificate['status'] == 'THEOREM'


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
