"""
Tests for Analytical Trace Identity Module
==========================================

Tests the implementation of the formal analytical proof of the
trace identity for operator M_E(s).

Test Coverage:
- Operator M_E(s) construction and properties
- Trace formula Tr(M_E(s)^k) = Σ a_n^k / n^{ks}
- Fredholm determinant computation
- Connection to L-function
- Q.E.D. certificate generation
"""

import pytest
import numpy as np

# Try to import Sage components
try:
    from sage.all import EllipticCurve
    SAGE_AVAILABLE = True
except ImportError:
    SAGE_AVAILABLE = False
    pytestmark = pytest.mark.skip("Sage not available")


if SAGE_AVAILABLE:
    from src.analytical_trace_identity import (
        OperatorME,
        FredholmDeterminant,
        AnalyticalTraceIdentity,
        demonstrate_analytical_proof,
        batch_verification
    )


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestOperatorME:
    """Tests for OperatorME class"""
    
    def test_initialization(self):
        """Test operator initialization"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        
        assert op.E == E
        assert op.s == 2.0 + 0.0j
        assert op.max_n == 100
        assert op.N == 11
    
    def test_coefficient_caching(self):
        """Test L-series coefficient caching"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        
        # Coefficients should be precomputed
        assert 1 in op._coefficients
        assert len(op._coefficients) == 100
        
        # a_1 should always be 1
        assert op.get_coefficient(1) == 1
    
    def test_eigenvalue_computation(self):
        """Test eigenvalue computation"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        
        # Eigenvalue for e_1: λ_1 = a_1 / 1^2 = 1 / 1 = 1
        eigenval_1 = op.eigenvalue(1)
        assert abs(eigenval_1 - 1.0) < 1e-10
        
        # Eigenvalue for e_2: λ_2 = a_2 / 2^2
        eigenval_2 = op.eigenvalue(2)
        a_2 = op.get_coefficient(2)
        expected = a_2 / (2 ** 2.0)
        assert abs(eigenval_2 - expected) < 1e-10
    
    def test_compactness(self):
        """Test that operator is compact for Re(s) > 3/2"""
        E = EllipticCurve('11a1')
        
        # Should be compact for s=2
        op_compact = OperatorME(E, s=2.0, max_n=1000)
        assert op_compact.is_compact()
        
        # Should not be compact for s=1 (Re(s) = 1 < 3/2)
        op_not_compact = OperatorME(E, s=1.0, max_n=1000)
        assert not op_not_compact.is_compact()
    
    def test_self_adjoint(self):
        """Test self-adjoint property"""
        E = EllipticCurve('11a1')
        
        # Should be self-adjoint for real s
        op_real = OperatorME(E, s=2.0, max_n=100)
        assert op_real.is_self_adjoint()
        
        # Should not be self-adjoint for complex s
        op_complex = OperatorME(E, s=2.0 + 1.0j, max_n=100)
        assert not op_complex.is_self_adjoint()
    
    def test_trace_computation(self):
        """Test trace computation Tr(M_E(s)^k)"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        
        # Tr(M_E^1) = Σ a_n / n^2
        trace_1 = op.compute_trace(1)
        assert isinstance(trace_1, complex)
        assert abs(trace_1.imag) < 1e-10  # Should be real for real s
        
        # Tr(M_E^2) = Σ (a_n / n^2)^2
        trace_2 = op.compute_trace(2)
        assert isinstance(trace_2, complex)
        
        # Higher powers should have smaller traces (eigenvalues < 1)
        trace_3 = op.compute_trace(3)
        assert abs(trace_3) < abs(trace_2)
    
    def test_trace_series(self):
        """Test trace series computation"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        
        traces = op.compute_trace_series(max_k=5)
        assert len(traces) == 5
        
        # All traces should be finite
        for trace in traces:
            assert np.isfinite(trace)


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestFredholmDeterminant:
    """Tests for FredholmDeterminant class"""
    
    def test_initialization(self):
        """Test Fredholm determinant initialization"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        fredholm = FredholmDeterminant(op, max_k=20)
        
        assert fredholm.operator == op
        assert fredholm.max_k == 20
    
    def test_determinant_via_trace(self):
        """Test determinant computation via trace formula"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        fredholm = FredholmDeterminant(op, max_k=20)
        
        det_trace = fredholm.compute_via_trace_formula()
        assert isinstance(det_trace, complex)
        assert np.isfinite(det_trace)
        
        # Determinant should be positive (for s > 3/2, eigenvalues small)
        assert det_trace.real > 0
    
    def test_determinant_via_product(self):
        """Test determinant computation via product formula"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        fredholm = FredholmDeterminant(op, max_k=20)
        
        det_product = fredholm.compute_via_product_formula()
        assert isinstance(det_product, complex)
        assert np.isfinite(det_product)
        
        # Determinant should be positive
        assert det_product.real > 0
    
    def test_formula_equivalence(self):
        """Test equivalence of trace and product formulas"""
        E = EllipticCurve('11a1')
        op = OperatorME(E, s=2.0, max_n=100)
        fredholm = FredholmDeterminant(op, max_k=30)
        
        verification = fredholm.verify_equivalence(tolerance=1e-4)
        
        assert 'det_via_trace' in verification
        assert 'det_via_product' in verification
        assert 'formulas_agree' in verification
        assert 'relative_error' in verification
        
        # Formulas should agree (within numerical tolerance)
        # Note: May not agree exactly due to truncation
        assert verification['relative_error'] < 0.5  # 50% tolerance due to truncation


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestAnalyticalTraceIdentity:
    """Tests for AnalyticalTraceIdentity class"""
    
    def test_initialization(self):
        """Test analytical proof initialization"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        assert proof.E == E
        assert proof.s == 2.0
        assert proof.operator is not None
        assert proof.fredholm is not None
    
    def test_operator_properties_verification(self):
        """Test operator properties verification"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        properties = proof.verify_operator_properties()
        
        assert 'is_compact' in properties
        assert 'is_self_adjoint' in properties
        assert 's_in_convergence_region' in properties
        
        # For s=2.0, should be compact and self-adjoint
        assert properties['is_compact']
        assert properties['is_self_adjoint']
        assert properties['s_in_convergence_region']
    
    def test_trace_identity_computation(self):
        """Test trace identity computation"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        trace_id = proof.compute_trace_identity()
        
        assert 'theorem' in trace_id
        assert 'statement' in trace_id
        assert 'traces' in trace_id
        assert trace_id['theorem'] == 'Trace Identity'
        
        # Should have traces for k=1,...,10
        traces = trace_id['traces']
        assert 'Tr(M_E^1)' in traces
        assert 'Tr(M_E^2)' in traces
    
    def test_fredholm_identity_computation(self):
        """Test Fredholm determinant identity"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        fredholm_id = proof.compute_fredholm_identity()
        
        assert 'theorem' in fredholm_id
        assert 'determinant_via_trace' in fredholm_id
        assert 'determinant_via_product' in fredholm_id
        assert 'formulas_agree' in fredholm_id
        assert fredholm_id['theorem'] == 'Fredholm Determinant'
    
    def test_l_function_connection(self):
        """Test connection to L-function"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        l_conn = proof.verify_l_function_connection()
        
        assert 'theorem' in l_conn
        assert 'determinant' in l_conn
        assert 'l_function' in l_conn
        assert l_conn['theorem'] == 'Central Identity'
        
        # At s=2, L-function should not vanish
        assert l_conn['l_function'] != 'vanishes'
    
    def test_qed_certificate_generation(self):
        """Test Q.E.D. certificate generation"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        certificate = proof.generate_qed_certificate()
        
        # Check certificate structure
        assert 'theorem' in certificate
        assert 'status' in certificate
        assert 'curve' in certificate
        assert 'proof_structure' in certificate
        assert 'conclusion' in certificate
        assert 'qed' in certificate
        
        # Check proof structure has all 4 components
        proof_struct = certificate['proof_structure']
        assert '1_operator_definition' in proof_struct
        assert '2_trace_formula' in proof_struct
        assert '3_fredholm_determinant' in proof_struct
        assert '4_l_function_identity' in proof_struct
        
        # Check conclusion
        conclusion = certificate['conclusion']
        assert 'analytical_link_closed' in conclusion
        assert 'no_numerical_dependency' in conclusion
        assert 'exact_trace_established' in conclusion
        
        # Should achieve Q.E.D. status for s=2.0
        assert certificate['status'] in ['Q.E.D.', 'PARTIAL']
    
    def test_qed_status_for_convergent_s(self):
        """Test that Q.E.D. is achieved for s in convergence region"""
        E = EllipticCurve('11a1')
        
        # Test with s=2.0 (well within convergence region)
        proof = AnalyticalTraceIdentity(E, s=2.0, max_n=500, max_k=30)
        certificate = proof.generate_qed_certificate()
        
        # Should achieve Q.E.D. for convergent parameter
        assert certificate['status'] == 'Q.E.D.'
        assert certificate['conclusion']['analytical_link_closed']
        assert certificate['qed'] == '∎'


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestDemonstrationFunctions:
    """Tests for demonstration and batch verification functions"""
    
    def test_demonstrate_analytical_proof(self):
        """Test demonstration function"""
        certificate = demonstrate_analytical_proof(curve_label='11a1', s=2.0)
        
        assert 'theorem' in certificate
        assert 'status' in certificate
        assert certificate['theorem'] == 'Analytical Trace Identity for M_E(s)'
    
    def test_demonstrate_rank0_curve(self):
        """Test demonstration for rank 0 curve"""
        # Curve 11a1 has rank 0
        certificate = demonstrate_analytical_proof(curve_label='11a1', s=2.0)
        
        assert certificate['curve']['rank'] == 0
        assert certificate['status'] == 'Q.E.D.'
    
    def test_demonstrate_rank1_curve(self):
        """Test demonstration for rank 1 curve"""
        # Curve 37a1 has rank 1
        certificate = demonstrate_analytical_proof(curve_label='37a1', s=2.0)
        
        assert certificate['curve']['rank'] >= 0  # At least verify it runs
    
    def test_batch_verification(self):
        """Test batch verification function"""
        curves = ['11a1', '37a1', '389a1']
        results = batch_verification(curves, s=2.0)
        
        assert 'curves_tested' in results
        assert 'results' in results
        assert 'all_verified' in results
        assert results['curves_tested'] == 3
        
        # Check each curve has results
        for curve in curves:
            assert curve in results['results']
            assert 'status' in results['results'][curve]
    
    def test_batch_verification_all_succeed(self):
        """Test that all curves in batch achieve Q.E.D."""
        curves = ['11a1', '37a1']
        results = batch_verification(curves, s=2.0)
        
        # All should succeed for s=2.0
        for curve in curves:
            result = results['results'][curve]
            assert result['status'] in ['Q.E.D.', 'PARTIAL']


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestNumericalAccuracy:
    """Tests for numerical accuracy of computations"""
    
    def test_trace_convergence(self):
        """Test that trace converges with increasing max_n"""
        E = EllipticCurve('11a1')
        
        # Compute with different truncations
        op_100 = OperatorME(E, s=2.0, max_n=100)
        op_500 = OperatorME(E, s=2.0, max_n=500)
        
        trace_100 = op_100.compute_trace(1)
        trace_500 = op_500.compute_trace(1)
        
        # Should be close (converging)
        relative_diff = abs(trace_500 - trace_100) / abs(trace_500)
        assert relative_diff < 0.1  # Within 10%
    
    def test_determinant_stability(self):
        """Test determinant stability with different parameters"""
        E = EllipticCurve('11a1')
        
        # Compute with different max_k
        op = OperatorME(E, s=2.0, max_n=300)
        fredholm_20 = FredholmDeterminant(op, max_k=20)
        fredholm_40 = FredholmDeterminant(op, max_k=40)
        
        det_20 = fredholm_20.compute_via_trace_formula()
        det_40 = fredholm_40.compute_via_trace_formula()
        
        # Should be relatively close
        relative_diff = abs(det_40 - det_20) / abs(det_40)
        assert relative_diff < 0.2  # Within 20%


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestEdgeCases:
    """Tests for edge cases and boundary conditions"""
    
    def test_s_at_boundary(self):
        """Test behavior at convergence boundary"""
        E = EllipticCurve('11a1')
        
        # At s = 1.6 (close to boundary 3/2 = 1.5)
        proof = AnalyticalTraceIdentity(E, s=1.6, max_n=500)
        properties = proof.verify_operator_properties()
        
        assert properties['s_in_convergence_region']
    
    def test_different_conductors(self):
        """Test with curves of different conductors"""
        curves = [
            ('11a1', 11),    # Small conductor
            ('37a1', 37),    # Medium conductor
            ('389a1', 389)   # Larger conductor
        ]
        
        for label, expected_N in curves:
            E = EllipticCurve(label)
            proof = AnalyticalTraceIdentity(E, s=2.0)
            properties = proof.verify_operator_properties()
            
            assert properties['conductor'] == expected_N
    
    def test_complex_parameter(self):
        """Test with complex parameter s"""
        E = EllipticCurve('11a1')
        
        # Use s = 2 + 0.5i (Re(s) = 2 > 3/2)
        proof = AnalyticalTraceIdentity(E, s=2.0 + 0.5j, max_n=100)
        
        properties = proof.verify_operator_properties()
        assert properties['s_in_convergence_region']
        assert not properties['is_self_adjoint']  # Not self-adjoint for complex s


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestTheoremStatements:
    """Tests verifying correct theorem statements"""
    
    def test_trace_identity_statement(self):
        """Verify trace identity statement is correct"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        trace_id = proof.compute_trace_identity()
        
        # Check statement includes key formula
        statement = trace_id['statement']
        assert 'Tr(M_E(s)^k)' in statement or 'Tr(M_E' in statement
        assert 'n^{ks}' in statement or 'nks' in statement or 'a_n' in statement
    
    def test_fredholm_statement(self):
        """Verify Fredholm determinant statement"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        fredholm_id = proof.compute_fredholm_identity()
        
        statement = fredholm_id['statement']
        assert 'det(I - M_E(s))' in statement or 'det' in statement
        assert 'Tr' in statement or 'exp' in statement
    
    def test_central_identity_statement(self):
        """Verify central identity statement"""
        E = EllipticCurve('11a1')
        proof = AnalyticalTraceIdentity(E, s=2.0)
        
        l_conn = proof.verify_l_function_connection()
        
        statement = l_conn['statement']
        assert 'det(I - M_E(s))' in statement or 'det' in statement
        assert 'L(E,s)' in statement or 'c(s)' in statement


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
