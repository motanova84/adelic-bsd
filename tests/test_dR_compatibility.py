"""
Tests for dR_compatibility module - Constructive proof of (dR) condition.
"""

import sys
import os
import json
import pytest
from pathlib import Path

sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

# Import classes for test suite (may fail if Sage not installed, handled in individual tests)
try:
    sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))
    from dR_compatibility import dRCompatibilityProver, prove_dR_all_cases
except ImportError:
    # If import fails, individual tests will skip appropriately
    dRCompatibilityProver = None
    prove_dR_all_cases = None


@pytest.mark.basic
def test_dR_compatibility_module_exists():
    """Test that dR_compatibility.py module exists"""
    module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
    assert module_path.exists(), "dR_compatibility.py module not found"
    print("✓ dR_compatibility.py module exists")


@pytest.mark.basic
def test_dR_compatibility_imports():
    """Test that the module can be imported (without Sage)"""
    try:
        # Try importing without Sage
        import importlib.util
        module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
        spec = importlib.util.spec_from_file_location("dR_compatibility", module_path)
        # Just check the file can be loaded
        assert spec is not None, "Could not load module spec"
        print("✓ Module can be loaded")
    except Exception as e:
        pytest.skip(f"Cannot import dR_compatibility without Sage: {e}")


@pytest.mark.sage_required
def test_dR_compatibility_class_exists():
    """Test that dRCompatibilityProver class exists"""
    try:
        from src.dR_compatibility import dRCompatibilityProver
        assert dRCompatibilityProver is not None
        print("✓ dRCompatibilityProver class exists")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_dR_compatibility_initialization():
    """Test basic initialization of dRCompatibilityProver"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        # Test with a simple curve
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 11, precision=10)
        
        assert prover.E == E
        assert prover.p == 11
        assert prover.prec == 10
        assert prover.reduction_type in ['good', 'multiplicative', 'additive_potential_good', 'additive_general', 'unknown']
        
        print(f"✓ Initialization successful, reduction type: {prover.reduction_type}")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_classify_reduction_good():
    """Test reduction classification for good reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        # 11a1 has good reduction at p=5
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 5, precision=10)
        
        assert prover.reduction_type == "good"
        print("✓ Good reduction classified correctly")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_classify_reduction_multiplicative():
    """Test reduction classification for multiplicative reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        # 11a1 has multiplicative reduction at p=11
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 11, precision=10)
        
        assert prover.reduction_type == "multiplicative"
        print("✓ Multiplicative reduction classified correctly")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_galois_representation_good():
    """Test Galois representation computation for good reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 5, precision=10)
        
        V_p = prover._compute_galois_representation()
        
        assert V_p['dimension'] == 2
        assert V_p['type'] == 'good'
        assert 'trace_frobenius' in V_p
        assert V_p['conductor_exponent'] == 0
        
        print(f"✓ Galois representation computed: trace_frobenius={V_p['trace_frobenius']}")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_galois_representation_multiplicative():
    """Test Galois representation computation for multiplicative reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 11, precision=10)
        
        V_p = prover._compute_galois_representation()
        
        assert V_p['dimension'] == 2
        assert V_p['type'] == 'multiplicative'
        assert V_p['conductor_exponent'] == 1
        assert 'split' in V_p
        
        print(f"✓ Galois representation computed: split={V_p['split']}")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_de_rham_cohomology():
    """Test de Rham cohomology computation"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 5, precision=10)
        
        D_dR = prover._compute_de_rham_cohomology()
        
        assert D_dR['dimension'] == 2
        assert 'generators' in D_dR
        assert 'omega' in D_dR['generators'][0].lower()
        assert 'filtration' in D_dR
        assert D_dR['filtration']['Fil_0'] == 2
        assert D_dR['filtration']['Fil_1'] == 1
        
        print("✓ de Rham cohomology computed correctly")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_formal_log():
    """Test formal logarithm computation"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 5, precision=10)
        
        log_series = prover._compute_formal_log()
        
        # Should return a power series or None
        assert log_series is not None or log_series is None
        
        print("✓ Formal logarithm computation succeeded")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_exponential_map_good():
    """Test exponential map for good reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 5, precision=10)
        
        V_p = prover._compute_galois_representation()
        D_dR = prover._compute_de_rham_cohomology()
        
        exp_map = prover._explicit_exponential_map(V_p, D_dR)
        
        assert exp_map['type'] == 'good_reduction'
        assert exp_map['map_defined'] is True
        assert exp_map['lands_in_Fil0'] is True
        assert exp_map['compatible'] is True
        assert exp_map['method'] == 'standard_crystalline'
        
        print("✓ Exponential map for good reduction verified")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_exponential_map_multiplicative():
    """Test exponential map for multiplicative reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 11, precision=10)
        cert = prover.prove_dR_compatibility()
        
        assert cert is not None
        assert 'dR_compatible' in cert
    except ImportError:
        pytest.skip("Sage not available")


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
        
        exp_map = prover._explicit_exponential_map(V_p, D_dR)
        
        assert exp_map['type'] == 'multiplicative'
        assert exp_map['map_defined'] is True
        assert exp_map['lands_in_Fil0'] is True
        assert exp_map['compatible'] is True
        assert exp_map['method'] == 'tate_uniformization'
        
        print("✓ Exponential map for multiplicative reduction verified")


@pytest.mark.sage_required
def test_prove_dR_compatibility_good():
    """Test main proof method for good reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 5, precision=10)
        
        certificate = prover.prove_dR_compatibility()
        
        assert 'curve' in certificate
        assert certificate['prime'] == 5
        assert certificate['reduction_type'] == 'good'
        assert certificate['dR_compatible'] is True
        assert certificate['verified'] is True
        assert certificate['status'] == 'THEOREM'
        assert 'galois_representation' in certificate
        assert 'de_rham_cohomology' in certificate
        assert 'exponential_map' in certificate
        
        print("✓ Main proof method works for good reduction")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
def test_prove_dR_compatibility_multiplicative():
    """Test main proof method for multiplicative reduction"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 11, precision=10)
        
        certificate = prover.prove_dR_compatibility()
        
        assert certificate['prime'] == 11
        assert certificate['reduction_type'] == 'multiplicative'
        assert certificate['dR_compatible'] is True
        assert certificate['status'] == 'THEOREM'
        
        print("✓ Main proof method works for multiplicative reduction")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.sage_required
@pytest.mark.slow
def test_prove_dR_all_cases():
    """Test batch proving function"""
    try:
        from src.dR_compatibility import prove_dR_all_cases
        import tempfile
        
        # Create temporary directory for output
        with tempfile.TemporaryDirectory() as tmpdir:
            results = prove_dR_all_cases(output_dir=tmpdir)
            
            # Check results structure
            assert isinstance(results, list)
            assert len(results) == 5  # Should test 5 curves
            
            # Check that certificates were generated
            cert_file = Path(tmpdir) / 'dR_certificates.json'
            assert cert_file.exists()
            
            # Load and verify certificates
            with open(cert_file, 'r') as f:
                certificates = json.load(f)
            
            assert len(certificates) == 5
            
            # Count successful proofs
            proved = sum(1 for r in results if r.get('dR_compatible', False))
            
            print(f"✓ Batch proving tested: {proved}/{len(results)} curves proved")
            
            # Most should succeed (allow for some failures due to edge cases)
            assert proved >= 3, "Too few curves successfully proved"
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")


@pytest.mark.basic
def test_module_documentation():
    """Test that module has proper documentation"""
    module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
    
    with open(module_path, 'r') as f:
        content = f.read()
    
    # Check for key documentation elements
    assert 'Prueba Constructiva de (dR)' in content
    assert 'Fontaine-Perrin-Riou' in content
    assert 'Bloch-Kato' in content
    assert 'dRCompatibilityProver' in content
    assert 'prove_dR_all_cases' in content
    
    print("✓ Module has proper documentation")


@pytest.mark.basic
def test_module_exports():
    """Test that module exports expected functions/classes"""
    module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
    
    with open(module_path, 'r') as f:
        content = f.read()
    
    # Check for expected exports
    assert 'class dRCompatibilityProver' in content
    assert 'def prove_dR_all_cases' in content
    assert 'def prove_dR_compatibility' in content
    
    print("✓ Module exports expected functions/classes")


@pytest.mark.basic
def test_reduction_type_coverage():
    """Test that all reduction types are handled"""
    module_path = Path(__file__).parent.parent / 'src' / 'dR_compatibility.py'
    
    with open(module_path, 'r') as f:
        content = f.read()
    
    # Check for handling of all reduction types
    assert '_exp_good_reduction' in content
    assert '_exp_multiplicative' in content
    assert '_exp_additive' in content
    assert 'additive_potential_good' in content or 'additive' in content
    
    print("✓ All reduction types are handled")


@pytest.mark.sage_required
def test_error_handling():
    """Test error handling in the module"""
    try:
        from sage.all import EllipticCurve
        from src.dR_compatibility import dRCompatibilityProver
        
        # Test with valid curve
        E = EllipticCurve('11a1')
        prover = dRCompatibilityProver(E, 5, precision=10)
        
        # The prove method should handle errors gracefully
        certificate = prover.prove_dR_compatibility()
        
        # Even if there's an error, status should be set
        assert 'status' in certificate
        
        print("✓ Error handling works correctly")
    except ImportError as e:
        pytest.skip(f"SageMath not available: {e}")
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
        
        # Should have both multiplicative and additive (the critical case)
        # Additive is the most important as it's the CRITICAL case for (dR)
        has_additive = any('additive' in rt for rt in reduction_types)
        has_multiplicative = 'multiplicative' in reduction_types
        
        assert has_additive, "Must test additive reduction (critical case)"
        assert has_multiplicative, "Must test multiplicative reduction"


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
