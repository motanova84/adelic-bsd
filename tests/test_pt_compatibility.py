"""
Tests for PT compatibility module
"""

import pytest
import json
from pathlib import Path
import sys

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from PT_compatibility import PTCompatibilityProver, prove_PT_all_ranks


class TestPTCompatibilityProver:
    """Test suite for PT compatibility prover"""
    
    def test_init(self):
        """Test initialization of PT prover"""
        prover = PTCompatibilityProver('389a1')
        assert prover.curve_label == '389a1'
        assert prover.conductor == 389
        assert prover.rank >= 0
    
    def test_rank_estimation(self):
        """Test rank estimation"""
        test_cases = {
            '11a1': 0,
            '37a1': 1,
            '389a1': 2,
            '5077a1': 3,
        }
        
        for label, expected_rank in test_cases.items():
            prover = PTCompatibilityProver(label)
            assert prover.rank == expected_rank
    
    def test_compute_selmer_group(self):
        """Test Selmer group computation"""
        prover = PTCompatibilityProver('37a1')
        selmer = prover.compute_selmer_group(p=2)
        
        assert 'dimension' in selmer
        assert 'prime' in selmer
        assert selmer['prime'] == 2
        assert selmer['dimension'] >= prover.rank
    
    def test_compute_analytic_rank(self):
        """Test analytic rank computation"""
        prover = PTCompatibilityProver('389a1')
        r_an = prover.compute_analytic_rank()
        
        # Should match algebraic rank (BSD prediction)
        assert r_an == prover.rank
    
    def test_height_pairing_symmetric(self):
        """Test that height pairing is symmetric"""
        prover = PTCompatibilityProver('389a1')
        
        h_01 = prover.compute_height_pairing(0, 1)
        h_10 = prover.compute_height_pairing(1, 0)
        
        # Should be symmetric (with numerical tolerance)
        assert abs(h_01 - h_10) < 1e-6
    
    def test_height_pairing_positive_diagonal(self):
        """Test that diagonal heights are positive"""
        prover = PTCompatibilityProver('389a1')
        
        for i in range(prover.rank):
            h_ii = prover.compute_height_pairing(i, i)
            assert h_ii > 0, f"Height <P_{i}, P_{i}> should be positive"
    
    def test_compute_regulator_rank_0(self):
        """Test regulator for rank 0"""
        prover = PTCompatibilityProver('11a1')
        reg = prover.compute_regulator()
        
        assert reg == 1.0
    
    def test_compute_regulator_rank_1(self):
        """Test regulator for rank 1"""
        prover = PTCompatibilityProver('37a1')
        reg = prover.compute_regulator()
        
        assert reg > 0
    
    def test_compute_regulator_rank_2(self):
        """Test regulator for rank 2 (CRITICAL for PT)"""
        prover = PTCompatibilityProver('389a1')
        reg = prover.compute_regulator()
        
        assert reg > 0, "Regulator must be positive for rank 2"
    
    def test_beilinson_bloch_heights(self):
        """Test Beilinson-Bloch height computation (CRITICAL)"""
        prover = PTCompatibilityProver('389a1')
        bb_heights = prover.compute_beilinson_bloch_height()
        
        assert 'beilinson_bloch_height' in bb_heights
        assert 'petersson_norm' in bb_heights
        assert 'L_derivative' in bb_heights
        assert 'regulator' in bb_heights
        
        # All values should be positive
        assert bb_heights['petersson_norm'] > 0
        assert bb_heights['regulator'] > 0
    
    def test_prove_PT_compatibility_rank_0(self):
        """Test PT proof for rank 0"""
        prover = PTCompatibilityProver('11a1')
        cert = prover.prove_PT_compatibility()
        
        assert cert['rank'] == 0
        assert cert['PT_compatible'] is True
        assert cert['method'] == 'trivial'
    
    def test_prove_PT_compatibility_rank_1(self):
        """Test PT proof for rank 1 (Gross-Zagier)"""
        prover = PTCompatibilityProver('37a1')
        cert = prover.prove_PT_compatibility()
        
        assert cert['rank'] == 1
        assert cert['PT_compatible'] is True
        assert cert['method'] == 'gross_zagier'
    
    def test_prove_PT_compatibility_rank_2(self):
        """Test PT proof for rank 2 (Yuan-Zhang-Zhang)"""
        prover = PTCompatibilityProver('389a1')
        cert = prover.prove_PT_compatibility()
        
        assert cert['rank'] == 2
        assert cert['PT_compatible'] is True
        assert cert['method'] == 'YZZ_beilinson_bloch'
    
    def test_prove_PT_compatibility_rank_3(self):
        """Test PT proof for rank 3"""
        prover = PTCompatibilityProver('5077a1')
        cert = prover.prove_PT_compatibility()
        
        assert cert['rank'] == 3
        assert cert['PT_compatible'] is True
        assert cert['method'] == 'YZZ_beilinson_bloch'


class TestPTAllRanks:
    """Test proving PT for all ranks"""
    
    def test_prove_all_ranks(self):
        """Test proving PT for ranks 0,1,2,3"""
        results = prove_PT_all_ranks()
        
        assert len(results) == 4
        assert all(r['PT_compatible'] for r in results)
        assert all(r['verified'] for r in results)
    
    def test_certificate_generation(self):
        """Test certificate file generation"""
        prove_PT_all_ranks()
        
        cert_file = Path('proofs/PT_certificates.json')
        assert cert_file.exists()
        
        with open(cert_file) as f:
            certs = json.load(f)
        
        assert isinstance(certs, list)
        assert len(certs) == 4
    
    def test_all_ranks_covered(self):
        """Test that ranks 0,1,2,3 are all covered"""
        results = prove_PT_all_ranks()
        
        ranks = [r['rank'] for r in results]
        
        assert 0 in ranks
        assert 1 in ranks
        assert 2 in ranks
        assert 3 in ranks
    
    def test_methods_appropriate(self):
        """Test that appropriate methods are used for each rank"""
        results = prove_PT_all_ranks()
        
        for result in results:
            rank = result['rank']
            method = result['method']
            
            if rank == 0:
                assert method == 'trivial'
            elif rank == 1:
                assert method == 'gross_zagier'
            else:
                assert method == 'YZZ_beilinson_bloch'


class TestPTIntegration:
    """Integration tests for PT compatibility"""
    
    def test_certificate_structure(self):
        """Test that certificates have required structure"""
        prover = PTCompatibilityProver('389a1')
        cert = prover.prove_PT_compatibility()
        
        required_fields = ['curve', 'rank', 'dim_selmer', 
                          'analytic_rank', 'PT_compatible', 'method', 'verified']
        
        for field in required_fields:
            assert field in cert, f"Missing field: {field}"
    
    def test_selmer_dimension_bounds(self):
        """Test that Selmer dimension is reasonable"""
        results = prove_PT_all_ranks()
        
        for result in results:
            dim_sel = result['dim_selmer']
            rank = result['rank']
            
            # Selmer dimension should be at least the rank
            assert dim_sel >= rank
    
    def test_compatibility_verification(self):
        """Test that PT compatibility is verified correctly"""
        results = prove_PT_all_ranks()
        
        for result in results:
            # All test cases should be compatible
            assert result['PT_compatible'] is True
            assert result['verified'] is True


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
