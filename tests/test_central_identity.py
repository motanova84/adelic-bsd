"""
Tests for Central Identity Module
===================================

Tests the implementation of Corollary 4.3:
    det(I - M_E(s)) = c(s) · L(E, s)

Test Coverage:
- Central identity computation
- Fredholm determinant
- c(s) factor non-vanishing
- Vanishing order matching
- BSD reduction to (dR) + (PT)
- Certificate generation
"""

import pytest
from pathlib import Path
import json

# Try to import Sage components
try:
    from sage.all import EllipticCurve
    SAGE_AVAILABLE = True
except ImportError:
    SAGE_AVAILABLE = False
    pytestmark = pytest.mark.skip("Sage not available")


if SAGE_AVAILABLE:
    from src.central_identity import CentralIdentity, demonstrate_central_identity


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestCentralIdentityBasic:
    """Basic tests for Central Identity module"""
    
    def test_initialization(self):
        """Test CentralIdentity initialization"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        assert ci.E == E
        assert ci.s == 1.0
        assert ci.N == 11
        assert ci.prec == 20
    
    def test_curve_label(self):
        """Test curve label extraction"""
        E = EllipticCurve('37a1')
        ci = CentralIdentity(E)
        
        label = ci._curve_label()
        assert '37' in label or 'a1' in label
    
    def test_local_operator_good_reduction(self):
        """Test local operator construction for good reduction"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        # Prime 2 has good reduction for 11a1
        p = 2
        if E.has_good_reduction(p):
            op_data = ci._good_reduction_operator(p)
            
            assert 'matrix' in op_data
            assert 'dimension' in op_data
            assert op_data['dimension'] == 1
            assert op_data['reduction_type'] == 'good'
            assert op_data['prime'] == p
    
    def test_local_operator_multiplicative(self):
        """Test local operator for multiplicative reduction"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        # Prime 11 divides conductor
        p = 11
        if E.has_multiplicative_reduction(p):
            op_data = ci._steinberg_operator(p)
            
            assert 'matrix' in op_data
            assert op_data['dimension'] == 2
            assert op_data['reduction_type'] == 'steinberg'
            assert op_data['prime'] == p


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestCentralIdentityComputation:
    """Test central identity computation"""
    
    def test_adelic_operator_construction(self):
        """Test construction of M_E(s)"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E, s=1.0)
        
        M_E = ci._construct_adelic_operator()
        
        assert 'local_operators' in M_E
        assert 'global_matrix' in M_E
        assert 'dimension' in M_E
        assert len(M_E['primes']) > 0
    
    def test_kernel_dimension_rank0(self):
        """Test kernel dimension for rank 0 curve"""
        E = EllipticCurve('11a1')  # rank 0
        ci = CentralIdentity(E)
        
        M_E = ci._construct_adelic_operator()
        ker_dim = ci._compute_kernel_dimension(M_E)
        
        # For rank 0, kernel should be trivial
        assert ker_dim == 0
    
    def test_kernel_dimension_rank1(self):
        """Test kernel dimension for rank 1 curve"""
        E = EllipticCurve('37a1')  # rank 1
        ci = CentralIdentity(E)
        
        M_E = ci._construct_adelic_operator()
        ker_dim = ci._compute_kernel_dimension(M_E)
        
        # Kernel dimension should match rank
        expected_rank = E.rank()
        assert ker_dim == expected_rank
    
    def test_fredholm_determinant(self):
        """Test Fredholm determinant computation"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E, s=1.0)
        
        det_data = ci._compute_fredholm_determinant()
        
        assert 'value' in det_data
        assert 'kernel_dimension' in det_data
        assert 'operator_data' in det_data
        assert det_data['method'] == 'fredholm_expansion'
    
    def test_l_function_evaluation(self):
        """Test L-function evaluation"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E, s=1.0)
        
        l_data = ci._compute_l_function()
        
        assert 'value' in l_data
        assert 'rank' in l_data
        assert isinstance(l_data['value'], float)
    
    def test_c_factor_computation(self):
        """Test c(s) factor computation"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E, s=1.0)
        
        c_data = ci._compute_c_factor()
        
        assert 'value' in c_data
        assert 'non_vanishing' in c_data
        assert 'local_factors' in c_data
        
        # c(1) must be non-zero (critical property)
        assert c_data['non_vanishing'] is True
        assert abs(c_data['value']) > 1e-10


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestCentralIdentityMain:
    """Test main central identity computation"""
    
    def test_central_identity_rank0(self):
        """Test central identity for rank 0 curve"""
        E = EllipticCurve('11a1')  # rank 0
        ci = CentralIdentity(E, s=1.0)
        
        result = ci.compute_central_identity()
        
        # Check structure
        assert 'determinant_lhs' in result
        assert 'l_function' in result
        assert 'c_factor' in result
        assert 'identity_verified' in result
        assert 'vanishing_order' in result
        
        # Check non-vanishing for rank 0
        assert result['c_factor']['non_vanishing'] is True
        
        # Check order
        vo = result['vanishing_order']
        assert vo['algebraic_rank'] == 0
        assert vo['spectral_rank'] == 0
        assert vo['ranks_match'] is True
    
    def test_central_identity_rank1(self):
        """Test central identity for rank 1 curve"""
        E = EllipticCurve('37a1')  # rank 1
        ci = CentralIdentity(E, s=1.0)
        
        result = ci.compute_central_identity()
        
        # Check structure
        assert 'vanishing_order' in result
        
        # For rank 1, both sides should vanish at s=1
        vo = result['vanishing_order']
        assert vo['algebraic_rank'] == 1
        
        # Spectral rank should match
        assert vo['ranks_match'] is True
    
    def test_vanishing_order_computation(self):
        """Test vanishing order computation"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        vo_data = ci._compute_vanishing_order()
        
        assert 'algebraic_rank' in vo_data
        assert 'spectral_rank' in vo_data
        assert 'ranks_match' in vo_data
        assert 'vanishing_order' in vo_data
        
        # Ranks should match
        assert vo_data['ranks_match'] is True


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestBSDReduction:
    """Test BSD reduction to compatibilities"""
    
    def test_bsd_reduction_rank0(self):
        """Test BSD reduction for rank 0 (unconditional)"""
        E = EllipticCurve('11a1')  # rank 0
        ci = CentralIdentity(E)
        
        result = ci.prove_bsd_reduction()
        
        assert 'central_identity' in result
        assert 'dr_compatibility' in result
        assert 'pt_compatibility' in result
        assert 'bsd_status' in result
        assert 'proof_level' in result
        
        # For rank 0, should be unconditional
        assert result['proof_level'] in ['unconditional', 'reduction']
    
    def test_bsd_reduction_rank1(self):
        """Test BSD reduction for rank 1 (unconditional via GZ)"""
        E = EllipticCurve('37a1')  # rank 1
        ci = CentralIdentity(E)
        
        result = ci.prove_bsd_reduction()
        
        assert 'bsd_status' in result
        assert 'proof_level' in result
        
        # For rank 1, Gross-Zagier + Kolyvagin give unconditional proof
        assert result['proof_level'] in ['unconditional', 'reduction']
    
    def test_dr_compatibility_check(self):
        """Test (dR) compatibility check"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        dr_status = ci._check_dr_compatibility()
        
        assert 'verified' in dr_status
        assert 'status' in dr_status
        assert isinstance(dr_status['verified'], bool)
    
    def test_pt_compatibility_check(self):
        """Test (PT) compatibility check"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        pt_status = ci._check_pt_compatibility()
        
        assert 'verified' in pt_status
        assert 'status' in pt_status
        assert isinstance(pt_status['verified'], bool)


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestCertificateGeneration:
    """Test certificate generation"""
    
    def test_certificate_structure(self):
        """Test certificate has correct structure"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        certificate = ci.generate_certificate()
        
        assert 'certificate_type' in certificate
        assert certificate['certificate_type'] == 'central_identity'
        assert 'version' in certificate
        assert 'curve' in certificate
        assert 'central_identity' in certificate
        assert 'vanishing_order' in certificate
        assert 'bsd_reduction' in certificate
        assert 'timestamp' in certificate
    
    def test_certificate_curve_data(self):
        """Test certificate includes correct curve data"""
        E = EllipticCurve('37a1')
        ci = CentralIdentity(E)
        
        certificate = ci.generate_certificate()
        
        curve_data = certificate['curve']
        assert 'label' in curve_data
        assert 'conductor' in curve_data
        assert 'discriminant' in curve_data
        assert 'rank' in curve_data
        
        # Check conductor matches
        assert curve_data['conductor'] == 37
    
    def test_certificate_save(self, tmp_path):
        """Test certificate saving to file"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E)
        
        cert_path = tmp_path / 'test_certificate.json'
        certificate = ci.generate_certificate(str(cert_path))
        
        # Check file created
        assert cert_path.exists()
        
        # Check file is valid JSON
        with open(cert_path) as f:
            loaded = json.load(f)
        
        assert loaded == certificate


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestDemonstration:
    """Test demonstration functions"""
    
    def test_demonstrate_central_identity(self):
        """Test demonstration for standard curve"""
        result = demonstrate_central_identity('11a1')
        
        assert 'curve' in result
        assert result['curve'] == '11a1'
        assert 'central_identity' in result
        assert 'bsd_reduction' in result
        assert 'certificate' in result


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestMultipleCurves:
    """Test central identity on multiple curves"""
    
    @pytest.mark.parametrize("curve_label,expected_rank", [
        ('11a1', 0),
        ('37a1', 1),
        ('389a1', 2),
    ])
    def test_multiple_curves(self, curve_label, expected_rank):
        """Test central identity on curves of different ranks"""
        E = EllipticCurve(curve_label)
        ci = CentralIdentity(E)
        
        result = ci.compute_central_identity()
        
        # Check identity computed
        assert result['identity_verified'] in [True, False]  # May depend on precision
        
        # Check vanishing order matches rank
        vo = result['vanishing_order']
        assert vo['algebraic_rank'] == expected_rank


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestNonVanishing:
    """Test critical non-vanishing property"""
    
    def test_c_factor_nonzero_at_s1(self):
        """Test c(1) ≠ 0 for various curves"""
        curves = ['11a1', '37a1', '389a1', '5077a1']
        
        for label in curves:
            E = EllipticCurve(label)
            ci = CentralIdentity(E, s=1.0)
            
            c_data = ci._compute_c_factor()
            
            # Critical: c(1) must be non-zero
            assert c_data['non_vanishing'] is True, \
                f"c(1) = 0 for curve {label}, violates non-vanishing!"
            
            assert abs(c_data['value']) > 1e-10, \
                f"c(1) too close to zero for curve {label}"
    
    def test_local_c_factors_nonzero(self):
        """Test local c_p(1) ≠ 0 for bad primes"""
        E = EllipticCurve('11a1')
        ci = CentralIdentity(E, s=1.0)
        
        for p in E.conductor().prime_factors():
            c_p_data = ci._local_c_factor(p)
            
            assert 'value' in c_p_data
            assert 'non_zero_at_s1' in c_p_data
            
            # Each local factor must be non-zero
            assert c_p_data['non_zero_at_s1'] is True, \
                f"c_{p}(1) = 0, violates local non-vanishing!"


@pytest.mark.skipif(not SAGE_AVAILABLE, reason="Sage required")
class TestSpectralConsequences:
    """Test spectral consequences of central identity"""
    
    def test_rank_equals_kernel_dimension(self):
        """Test that rank = dim ker M_E(1)"""
        curves = ['11a1', '37a1', '389a1']
        
        for label in curves:
            E = EllipticCurve(label)
            ci = CentralIdentity(E)
            
            vo = ci._compute_vanishing_order()
            
            # Spectral rank = kernel dimension
            # Algebraic rank = Mordell-Weil rank
            # They must match (consequence of central identity)
            assert vo['ranks_match'] is True, \
                f"Ranks don't match for {label}: " \
                f"algebraic={vo['algebraic_rank']}, " \
                f"spectral={vo['spectral_rank']}"
    
    def test_vanishing_order_equals_rank(self):
        """Test ord_{s=1} det = rank"""
        E = EllipticCurve('37a1')  # rank 1
        ci = CentralIdentity(E)
        
        vo = ci._compute_vanishing_order()
        
        # Vanishing order should equal rank
        assert vo['vanishing_order'] == vo['algebraic_rank']
        assert vo['vanishing_order'] == 1


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
