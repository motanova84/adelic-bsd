"""
Tests for spectral finiteness proof
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

def test_11a1_finiteness():
    """Test finiteness proof for curve 11a1"""
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()
    
    assert result['finiteness_proved'] == True
    assert result['global_bound'] >= 1  # Known: #Ш = 1
    print("✓ 11a1: finiteness proved")

def test_multiple_curves():
    """Test finiteness for multiple curves"""
    test_curves = ['11a1', '11a2', '14a1', '15a1']
    
    for label in test_curves:
        E = EllipticCurve(label)
        prover = SpectralFinitenessProver(E)
        result = prover.prove_finiteness()
        
        assert result['finiteness_proved'] == True
        print(f"✓ {label}: finiteness proved, bound = {result['global_bound']}")

def test_certificate_generation():
    """Test certificate generation"""
    E = EllipticCurve('11a1')
    prover = SpectralFinitenessProver(E)
    
    # Test text certificate
    cert = prover.generate_certificate('text')
    assert 'SPECTRAL FINITENESS CERTIFICATE' in cert
    assert 'PROVED' in cert
    print("✓ Certificate generation works")

def run_all_tests():
    """Run all tests"""
    print("Running Spectral Finiteness Tests...")
    print("=" * 50)
    
    test_11a1_finiteness()
    test_multiple_curves() 
    test_certificate_generation()
    
    print("=" * 50)
    print("🎉 ALL TESTS PASSED!")

if __name__ == "__main__":
    run_all_tests()
