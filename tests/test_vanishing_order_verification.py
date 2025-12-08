"""
Tests for Vanishing Order Verification Module
==============================================

Tests the implementation of the vanishing order identity:
    ord_{s=1} det(I - K_E(s)) = ord_{s=1} Λ(E, s) = r(E)

Test Coverage:
- Vanishing order computation for different ranks
- Spectral rank vs algebraic rank matching
- c-factor non-vanishing verification
- Batch verification of multiple curves
"""

import pytest

# Try to import SageMath
try:
    from sage.all import EllipticCurve
    SAGE_AVAILABLE = True
except ImportError:
    SAGE_AVAILABLE = False

# Import module to test
try:
    from src.vanishing_order_verification import (
        VanishingOrderVerifier,
        VanishingOrderResult,
        verify_vanishing_order_for_curve,
        batch_verify_vanishing_orders
    )
    MODULE_AVAILABLE = True
except ImportError:
    MODULE_AVAILABLE = False


# Skip all tests if dependencies not available
pytestmark = pytest.mark.skipif(
    not (SAGE_AVAILABLE and MODULE_AVAILABLE),
    reason="SageMath or vanishing_order_verification module not available"
)


class TestVanishingOrderVerifier:
    """Test VanishingOrderVerifier class"""
    
    @pytest.fixture
    def verifier_rank0(self):
        """Create verifier for rank 0 curve"""
        return VanishingOrderVerifier('11a1', verbose=False)
    
    @pytest.fixture
    def verifier_rank1(self):
        """Create verifier for rank 1 curve"""
        return VanishingOrderVerifier('37a1', verbose=False)
    
    def test_initialization_from_label(self):
        """Test initialization with curve label"""
        verifier = VanishingOrderVerifier('11a1', verbose=False)
        assert verifier.curve_label == '11a1'
        assert verifier.N == 11
        assert verifier.precision == 20
    
    def test_initialization_from_curve(self):
        """Test initialization with EllipticCurve object"""
        E = EllipticCurve('37a1')
        verifier = VanishingOrderVerifier(E, verbose=False)
        assert verifier.E == E
        assert verifier.N == 37
    
    def test_algebraic_rank_computation(self, verifier_rank0, verifier_rank1):
        """Test algebraic rank computation"""
        # Rank 0 curve
        r0 = verifier_rank0.compute_algebraic_rank()
        assert r0 == 0
        
        # Rank 1 curve
        r1 = verifier_rank1.compute_algebraic_rank()
        assert r1 == 1
    
    def test_analytic_rank_computation(self, verifier_rank0, verifier_rank1):
        """Test analytic rank computation"""
        # Rank 0 curve
        r_an0 = verifier_rank0.compute_analytic_rank()
        assert r_an0 == 0
        
        # Rank 1 curve
        r_an1 = verifier_rank1.compute_analytic_rank()
        assert r_an1 == 1
    
    def test_spectral_rank_computation(self, verifier_rank0):
        """Test spectral rank computation"""
        r_sp = verifier_rank0.compute_spectral_rank()
        assert isinstance(r_sp, int)
        assert r_sp >= 0
    
    def test_l_function_vanishing_order(self, verifier_rank0, verifier_rank1):
        """Test L-function vanishing order"""
        # Rank 0: L(E,1) ≠ 0
        ord0 = verifier_rank0.compute_l_function_vanishing_order()
        assert ord0 == 0
        
        # Rank 1: L(E,1) = 0 with ord = 1
        ord1 = verifier_rank1.compute_l_function_vanishing_order()
        assert ord1 == 1
    
    def test_determinant_vanishing_order(self, verifier_rank0):
        """Test determinant vanishing order"""
        ord_det = verifier_rank0.compute_determinant_vanishing_order()
        assert isinstance(ord_det, int)
        assert ord_det >= 0
    
    def test_c_factor_computation(self, verifier_rank0):
        """Test c-factor computation"""
        c_value, c_nonzero = verifier_rank0.compute_c_factor_at_s1()
        
        assert isinstance(c_value, float)
        assert isinstance(c_nonzero, bool)
        # c(1) should be non-zero
        assert c_nonzero
        assert abs(c_value) > 1e-10


class TestVanishingOrderVerification:
    """Test complete vanishing order verification"""
    
    def test_verify_rank0_curve(self):
        """Test verification for rank 0 curve (11a1)"""
        result = verify_vanishing_order_for_curve('11a1', verbose=False)
        
        assert isinstance(result, VanishingOrderResult)
        assert result.success
        assert result.curve_label == '11a1'
        assert result.conductor == 11
        assert result.algebraic_rank == 0
        assert result.identity_verified
    
    def test_verify_rank1_curve(self):
        """Test verification for rank 1 curve (37a1)"""
        result = verify_vanishing_order_for_curve('37a1', verbose=False)
        
        assert result.success
        assert result.curve_label == '37a1'
        assert result.conductor == 37
        assert result.algebraic_rank == 1
        assert result.identity_verified
    
    def test_ranks_match(self):
        """Test that all ranks match for verified curves"""
        result = verify_vanishing_order_for_curve('11a1', verbose=False)
        
        assert result.ranks_match
        assert result.algebraic_rank == result.analytic_rank
        assert result.algebraic_rank == result.spectral_rank
    
    def test_orders_match_rank(self):
        """Test that vanishing orders equal the rank"""
        result = verify_vanishing_order_for_curve('11a1', verbose=False)
        
        assert result.orders_match
        assert result.l_function_order == result.algebraic_rank
        assert result.determinant_order == result.algebraic_rank
    
    def test_c_factor_nonvanishing(self):
        """Test that c-factor is non-vanishing"""
        result = verify_vanishing_order_for_curve('11a1', verbose=False)
        
        assert result.c_nonvanishing
        assert abs(result.c_at_s1) > 1e-10


class TestBatchVerification:
    """Test batch verification of multiple curves"""
    
    def test_batch_verify_small_set(self):
        """Test batch verification with small set of curves"""
        curves = ['11a1', '37a1']
        results = batch_verify_vanishing_orders(curves, verbose=False)
        
        assert len(results) == 2
        assert all(isinstance(r, VanishingOrderResult) for r in results.values())
        assert all(r.success for r in results.values())
    
    def test_batch_verify_different_ranks(self):
        """Test batch verification with curves of different ranks"""
        curves = ['11a1', '37a1', '389a1']  # ranks 0, 1, 2
        results = batch_verify_vanishing_orders(curves, verbose=False)
        
        assert len(results) == 3
        
        # Check ranks
        assert results['11a1'].algebraic_rank == 0
        assert results['37a1'].algebraic_rank == 1
        assert results['389a1'].algebraic_rank == 2
    
    def test_batch_verify_all_verified(self):
        """Test that all curves in batch are verified"""
        curves = ['11a1', '37a1']
        results = batch_verify_vanishing_orders(curves, verbose=False)
        
        assert all(r.identity_verified for r in results.values())
        assert all(r.ranks_match for r in results.values())
        assert all(r.orders_match for r in results.values())


class TestVanishingOrderResult:
    """Test VanishingOrderResult dataclass"""
    
    def test_result_structure(self):
        """Test that result has all expected fields"""
        result = verify_vanishing_order_for_curve('11a1', verbose=False)
        
        # Check all required fields exist
        assert hasattr(result, 'curve_label')
        assert hasattr(result, 'conductor')
        assert hasattr(result, 'algebraic_rank')
        assert hasattr(result, 'analytic_rank')
        assert hasattr(result, 'spectral_rank')
        assert hasattr(result, 'l_function_order')
        assert hasattr(result, 'determinant_order')
        assert hasattr(result, 'ranks_match')
        assert hasattr(result, 'orders_match')
        assert hasattr(result, 'identity_verified')
        assert hasattr(result, 'c_at_s1')
        assert hasattr(result, 'c_nonvanishing')
        assert hasattr(result, 'precision')
        assert hasattr(result, 'success')
    
    def test_result_types(self):
        """Test that result fields have correct types"""
        result = verify_vanishing_order_for_curve('11a1', verbose=False)
        
        assert isinstance(result.curve_label, str)
        assert isinstance(result.conductor, int)
        assert isinstance(result.algebraic_rank, int)
        assert isinstance(result.analytic_rank, int)
        assert isinstance(result.spectral_rank, int)
        assert isinstance(result.l_function_order, int)
        assert isinstance(result.determinant_order, int)
        assert isinstance(result.ranks_match, bool)
        assert isinstance(result.orders_match, bool)
        assert isinstance(result.identity_verified, bool)
        assert isinstance(result.c_at_s1, float)
        assert isinstance(result.c_nonvanishing, bool)
        assert isinstance(result.precision, int)
        assert isinstance(result.success, bool)


class TestEdgeCases:
    """Test edge cases and error handling"""
    
    def test_high_precision(self):
        """Test verification with high precision"""
        result = verify_vanishing_order_for_curve('11a1', precision=50, verbose=False)
        
        assert result.success
        assert result.precision == 50
    
    def test_different_curves(self):
        """Test verification for various curves"""
        test_curves = [
            ('11a1', 0),   # rank 0
            ('37a1', 1),   # rank 1
            ('389a1', 2),  # rank 2
        ]
        
        for label, expected_rank in test_curves:
            result = verify_vanishing_order_for_curve(label, verbose=False)
            assert result.success
            assert result.algebraic_rank == expected_rank


if __name__ == "__main__":
    pytest.main([__file__, '-v'])
