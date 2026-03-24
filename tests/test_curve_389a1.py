"""
Tests for BSD validation of curve 389a1

This module tests the BSD invariants and formula verification
for the elliptic curve 389a1.
"""

import json
import os
import pytest


# Path to the curves/proven directory
CURVES_DIR = os.path.join(os.path.dirname(__file__), '..', 'curves', 'proven')


class TestCurve389a1:
    """Tests for curve 389a1 BSD validation"""
    
    def test_proof_json_exists(self):
        """Test that proof.json exists"""
        proof_path = os.path.join(CURVES_DIR, 'proof.json')
        assert os.path.exists(proof_path), "proof.json should exist"
    
    def test_proof_json_valid(self):
        """Test that proof.json is valid JSON"""
        proof_path = os.path.join(CURVES_DIR, 'proof.json')
        with open(proof_path, 'r') as f:
            proof = json.load(f)
        
        assert 'curve' in proof
        assert 'invariants' in proof
        assert 'verification' in proof
        assert 'signature' in proof
    
    def test_curve_label(self):
        """Test curve label is correct"""
        proof_path = os.path.join(CURVES_DIR, 'proof.json')
        with open(proof_path, 'r') as f:
            proof = json.load(f)
        
        assert proof['curve']['label'] == '389a1'
        assert proof['curve']['conductor'] == 389
        assert proof['curve']['rank'] == 2
    
    def test_bsd_invariants(self):
        """Test BSD invariants are correct"""
        proof_path = os.path.join(CURVES_DIR, 'proof.json')
        with open(proof_path, 'r') as f:
            proof = json.load(f)
        
        inv = proof['invariants']
        
        assert inv['torsion_order'] == 1
        assert inv['tamagawa_product'] == 1
        assert inv['sha_analytic'] == 1.0
        assert inv['regulator'] > 0
        assert inv['real_period'] > 0
        assert inv['leading_term'] > 0
    
    def test_bsd_verification(self):
        """Test BSD formula verification"""
        proof_path = os.path.join(CURVES_DIR, 'proof.json')
        with open(proof_path, 'r') as f:
            proof = json.load(f)
        
        ver = proof['verification']
        
        assert ver['verified'] == True
        assert ver['relative_difference'] < ver['tolerance']
    
    def test_signature_status(self):
        """Test signature status is VALIDATED"""
        proof_path = os.path.join(CURVES_DIR, 'proof.json')
        with open(proof_path, 'r') as f:
            proof = json.load(f)
        
        sig = proof['signature']
        
        assert sig['status'] == 'VALIDATED_BSD_CURVE'
        assert len(sig['hash_sha256']) == 64  # SHA-256 hex digest
        assert sig['psi_symbiotic'] > 0.99
    
    def test_bsd_formula_calculation(self):
        """Test BSD formula calculation independently"""
        proof_path = os.path.join(CURVES_DIR, 'proof.json')
        with open(proof_path, 'r') as f:
            proof = json.load(f)
        
        inv = proof['invariants']
        
        # Calculate RHS independently
        rhs = (inv['real_period'] * inv['regulator'] * 
               inv['sha_analytic'] * inv['tamagawa_product']) / (inv['torsion_order'] ** 2)
        
        # Check it matches the stored value
        assert abs(rhs - proof['verification']['rhs']) < 1e-10
        
        # Check the difference
        lhs = inv['leading_term']
        relative_diff = abs(lhs - rhs) / lhs
        
        assert relative_diff < 1e-3  # Within 0.1%
    
    def test_lean_file_exists(self):
        """Test that Lean formalization exists"""
        lean_path = os.path.join(CURVES_DIR, 'lean', 'Curve389a1.lean')
        assert os.path.exists(lean_path), "Curve389a1.lean should exist"
    
    def test_notebook_exists(self):
        """Test that validation notebook exists"""
        notebook_path = os.path.join(CURVES_DIR, 'notebooks', 'validate_389a1.ipynb')
        assert os.path.exists(notebook_path), "validate_389a1.ipynb should exist"
    
    def test_notebook_valid(self):
        """Test that notebook is valid JSON (ipynb format)"""
        notebook_path = os.path.join(CURVES_DIR, 'notebooks', 'validate_389a1.ipynb')
        with open(notebook_path, 'r') as f:
            notebook = json.load(f)
        
        assert 'cells' in notebook
        assert 'metadata' in notebook
        assert 'nbformat' in notebook


class TestCurvesStructure:
    """Tests for the curves directory structure"""
    
    def test_proven_directory_exists(self):
        """Test that curves/proven directory exists"""
        assert os.path.exists(CURVES_DIR)
    
    def test_lean_directory_exists(self):
        """Test that lean subdirectory exists"""
        lean_dir = os.path.join(CURVES_DIR, 'lean')
        assert os.path.exists(lean_dir)
    
    def test_notebooks_directory_exists(self):
        """Test that notebooks subdirectory exists"""
        notebooks_dir = os.path.join(CURVES_DIR, 'notebooks')
        assert os.path.exists(notebooks_dir)
    
    def test_readme_exists(self):
        """Test that README exists"""
        readme_path = os.path.join(CURVES_DIR, 'README.md')
        assert os.path.exists(readme_path)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
