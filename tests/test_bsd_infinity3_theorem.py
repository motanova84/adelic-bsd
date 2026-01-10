"""
Tests for BSD ∞³ Theorem module.

This test suite verifies the BSD ∞³ theorem implementation including:
- Spectral frequency formula: f₀ = |ζ'(1/2)| · φ³ = 141.7001 Hz
- Golden ratio identities
- Certificate generation
- Theorem verification

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: December 2025
"""

import unittest
import math
from src.bsd_infinity3_theorem import (
    BSDInfinity3Theorem,
    BSDInfinity3Certificate,
    SpectralFrequencyResult,
    compute_spectral_frequency,
    compute_fundamental_constants,
    verify_golden_ratio_identity,
    verify_phi_cube_formula,
    demonstrate_bsd_infinity3,
    PHI,
    PHI_CUBED,
    ZETA_PRIME_HALF_ABS
)


class TestSpectralFrequency(unittest.TestCase):
    """Test spectral frequency computations."""

    def test_spectral_frequency_value(self):
        """Test that spectral frequency equals 141.7001 Hz."""
        result = compute_spectral_frequency()
        self.assertAlmostEqual(result.f0_hz, 141.7001, places=4)
    
    def test_spectral_frequency_verified(self):
        """Test that spectral frequency is verified."""
        result = compute_spectral_frequency()
        self.assertTrue(result.verified)
    
    def test_spectral_frequency_components(self):
        """Test spectral frequency components."""
        result = compute_spectral_frequency()
        
        # Check phi is golden ratio
        expected_phi = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(result.phi, expected_phi, places=10)
        
        # Check phi cubed
        self.assertAlmostEqual(result.phi_cubed, expected_phi ** 3, places=10)
        
        # Check zeta prime half - |ζ'(1/2)| ≈ 3.9226
        self.assertGreater(result.zeta_prime_half, 3)
        self.assertLess(result.zeta_prime_half, 4)


class TestFundamentalConstants(unittest.TestCase):
    """Test fundamental mathematical constants."""

    def test_compute_fundamental_constants(self):
        """Test that fundamental constants are computed correctly."""
        constants = compute_fundamental_constants()
        
        # Check all expected keys are present
        expected_keys = ['phi', 'phi_squared', 'phi_cubed', 
                        'zeta_prime_half_abs', 'f0_hz', 'omega_0']
        for key in expected_keys:
            self.assertIn(key, constants)
    
    def test_golden_ratio_value(self):
        """Test golden ratio value."""
        constants = compute_fundamental_constants()
        expected_phi = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(constants['phi'], expected_phi, places=10)
    
    def test_phi_squared_value(self):
        """Test phi squared value."""
        constants = compute_fundamental_constants()
        expected = constants['phi'] ** 2
        self.assertAlmostEqual(constants['phi_squared'], expected, places=10)
    
    def test_phi_cubed_value(self):
        """Test phi cubed value."""
        constants = compute_fundamental_constants()
        expected = constants['phi'] ** 3
        self.assertAlmostEqual(constants['phi_cubed'], expected, places=10)
    
    def test_f0_value(self):
        """Test f₀ = 141.7001 Hz."""
        constants = compute_fundamental_constants()
        self.assertEqual(constants['f0_hz'], 141.7001)
    
    def test_omega_0_value(self):
        """Test ω₀ = 2πf₀."""
        constants = compute_fundamental_constants()
        expected_omega = 2 * math.pi * 141.7001
        self.assertAlmostEqual(constants['omega_0'], expected_omega, places=6)


class TestGoldenRatioIdentities(unittest.TestCase):
    """Test golden ratio identities."""

    def test_phi_squared_identity(self):
        """Test φ² = φ + 1."""
        result = verify_golden_ratio_identity()
        
        self.assertTrue(result['verified'])
        self.assertLess(result['error'], 1e-10)
        self.assertEqual(result['identity'], 'φ² = φ + 1')
    
    def test_phi_cubed_identity(self):
        """Test φ³ = 2φ + 1."""
        result = verify_phi_cube_formula()
        
        self.assertTrue(result['verified'])
        self.assertLess(result['error'], 1e-10)
        self.assertEqual(result['identity'], 'φ³ = 2φ + 1')
    
    def test_phi_squared_numerical(self):
        """Test φ² = φ + 1 numerically."""
        phi = PHI
        phi_squared = phi ** 2
        phi_plus_one = phi + 1
        
        self.assertAlmostEqual(phi_squared, phi_plus_one, places=10)
    
    def test_phi_cubed_numerical(self):
        """Test φ³ = 2φ + 1 numerically."""
        phi = PHI
        phi_cubed = phi ** 3
        two_phi_plus_one = 2 * phi + 1
        
        self.assertAlmostEqual(phi_cubed, two_phi_plus_one, places=10)


class TestBSDInfinity3Theorem(unittest.TestCase):
    """Test BSD ∞³ Theorem class."""

    def setUp(self):
        """Set up test fixtures."""
        self.theorem = BSDInfinity3Theorem(verbose=False)
    
    def test_theorem_initialization(self):
        """Test theorem initializes correctly."""
        self.assertIsNotNone(self.theorem)
        self.assertIsNotNone(self.theorem.constants)
    
    def test_theorem_constants(self):
        """Test theorem has correct constants."""
        self.assertIn('phi', self.theorem.constants)
        self.assertIn('f0_hz', self.theorem.constants)
        self.assertEqual(self.theorem.constants['f0_hz'], 141.7001)
    
    def test_compute_spectral_frequency(self):
        """Test theorem computes spectral frequency."""
        result = self.theorem.compute_spectral_frequency()
        
        self.assertIsInstance(result, SpectralFrequencyResult)
        self.assertAlmostEqual(result.f0_hz, 141.7001, places=4)
        self.assertTrue(result.verified)
    
    def test_state_theorem(self):
        """Test theorem statement generation."""
        statement = self.theorem.state_theorem()
        
        self.assertIsInstance(statement, str)
        self.assertIn('BSD', statement)
        self.assertIn('K_E(s)', statement)
        self.assertIn('141.7001', statement)
        self.assertIn('det(I - K_E(s))', statement)
    
    def test_generate_certificate(self):
        """Test certificate generation."""
        cert = self.theorem.generate_certificate()
        
        self.assertIsInstance(cert, dict)
        self.assertIn('theorem', cert)
        self.assertIn('version', cert)
        self.assertIn('timestamp', cert)
        self.assertIn('spectral_identity', cert)
        self.assertIn('spectral_frequency', cert)
        self.assertIn('constants', cert)
    
    def test_certificate_spectral_frequency(self):
        """Test certificate contains correct spectral frequency."""
        cert = self.theorem.generate_certificate()
        
        freq = cert['spectral_frequency']
        self.assertAlmostEqual(freq['value_hz'], 141.7001, places=4)
        self.assertTrue(freq['verified'])
    
    def test_verify_spectral_frequency(self):
        """Test spectral frequency verification."""
        verification = self.theorem.verify_spectral_frequency()
        
        self.assertTrue(verification['verified'])
        self.assertEqual(verification['target_hz'], 141.7001)
        self.assertAlmostEqual(verification['computed_hz'], 141.7001, places=4)
        self.assertIn('VERIFIED', verification['status'])


class TestCertificateGeneration(unittest.TestCase):
    """Test certificate generation."""

    def setUp(self):
        """Set up test fixtures."""
        self.theorem = BSDInfinity3Theorem(verbose=False)
    
    def test_certificate_structure(self):
        """Test certificate has correct structure."""
        cert = self.theorem.generate_certificate()
        
        # Check top-level keys
        required_keys = [
            'theorem', 'version', 'timestamp',
            'spectral_identity', 'compatibilities',
            'spectral_frequency', 'constants', 'identities'
        ]
        for key in required_keys:
            self.assertIn(key, cert)
    
    def test_certificate_identities(self):
        """Test certificate contains verified identities."""
        cert = self.theorem.generate_certificate()
        
        identities = cert['identities']
        self.assertTrue(identities['phi_squared']['verified'])
        self.assertTrue(identities['phi_cubed']['verified'])
    
    def test_certificate_with_curve_data(self):
        """Test certificate generation with curve data."""
        curve_data = {
            'label': '11a1',
            'conductor': 11,
            'rank': 0
        }
        cert = self.theorem.generate_certificate(curve_data=curve_data)
        
        self.assertIn('curve_data', cert)
        self.assertEqual(cert['curve_data']['label'], '11a1')


class TestModuleConstants(unittest.TestCase):
    """Test module-level constants."""

    def test_phi_constant(self):
        """Test PHI constant."""
        expected = (1 + math.sqrt(5)) / 2
        self.assertAlmostEqual(PHI, expected, places=10)
    
    def test_phi_cubed_constant(self):
        """Test PHI_CUBED constant."""
        expected = PHI ** 3
        self.assertAlmostEqual(PHI_CUBED, expected, places=10)
    
    def test_zeta_prime_half_constant(self):
        """Test ZETA_PRIME_HALF_ABS constant."""
        # |ζ'(1/2)| ≈ 3.9226
        self.assertGreater(ZETA_PRIME_HALF_ABS, 3.9)
        self.assertLess(ZETA_PRIME_HALF_ABS, 4.0)


class TestDemonstration(unittest.TestCase):
    """Test demonstration function."""

    def test_demonstrate_bsd_infinity3(self):
        """Test demonstration runs without error."""
        result = demonstrate_bsd_infinity3()
        
        self.assertIsInstance(result, dict)
        self.assertIn('theorem', result)
        self.assertIn('verification', result)
        self.assertIn('certificate', result)
    
    def test_demonstration_verification(self):
        """Test demonstration verification result."""
        result = demonstrate_bsd_infinity3()
        
        verification = result['verification']
        self.assertTrue(verification['verified'])


if __name__ == '__main__':
    unittest.main()
