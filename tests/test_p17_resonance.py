"""
Unit tests for p17 resonance and spectral frequency mapping.

Tests the equilibrium function and verifies that p=17 is a resonance
point producing f₀ = 141.7001 Hz, not a minimum of equilibrium(p).

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: December 2025
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path to import p17_balance_optimality
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from p17_balance_optimality import (
    equilibrium,
    find_equilibrium_minimum,
    compute_spectral_frequency,
    frequency_to_note,
    generate_prime_spectral_map,
    verify_p17_resonance
)


class TestEquilibriumFunction(unittest.TestCase):
    """Test the equilibrium function."""

    def test_equilibrium_positive_input(self):
        """Test equilibrium with positive prime input."""
        result = equilibrium(17)
        self.assertTrue(np.isfinite(result))
        self.assertGreater(result, 0)

    def test_equilibrium_invalid_input(self):
        """Test that non-positive input raises ValueError."""
        with self.assertRaises(ValueError):
            equilibrium(0)
        with self.assertRaises(ValueError):
            equilibrium(-5)

    def test_equilibrium_small_primes(self):
        """Test equilibrium values for small primes."""
        primes = [2, 3, 5, 7, 11, 13, 17]
        for p in primes:
            eq = equilibrium(p)
            self.assertGreater(eq, 0, f"equilibrium({p}) should be positive")
            self.assertTrue(np.isfinite(eq), f"equilibrium({p}) should be finite")


class TestMinimumFinding(unittest.TestCase):
    """Test finding the minimum of equilibrium function."""

    def test_p17_not_minimum(self):
        """Verify that p=17 is NOT the minimum."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
        min_prime, min_value = find_equilibrium_minimum(primes)

        # p=17 should NOT be the minimum
        self.assertNotEqual(min_prime, 17,
                          "p=17 should NOT minimize equilibrium(p)")

    def test_p3_is_global_minimum(self):
        """Verify that p=3 is the global minimum among small primes."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
        min_prime, min_value = find_equilibrium_minimum(primes)

        # p=3 should be the minimum
        self.assertEqual(min_prime, 3,
                        "p=3 should minimize equilibrium(p) globally")

    def test_p11_is_local_minimum(self):
        """Verify that p=11 is minimum among primes >= 11."""
        primes = [11, 13, 17, 19, 23, 29]
        min_prime, min_value = find_equilibrium_minimum(primes)

        # p=11 should be the minimum in this range
        self.assertEqual(min_prime, 11,
                        "p=11 should minimize equilibrium(p) for p >= 11")


class TestSpectralFrequency(unittest.TestCase):
    """Test spectral frequency computation."""

    def test_compute_frequency_positive(self):
        """Test that computed frequency is positive."""
        freq = compute_spectral_frequency(17)
        self.assertGreater(freq, 0)
        self.assertTrue(np.isfinite(freq))

    def test_p17_yields_141hz(self):
        """Test that p=17 produces approximately 141.7 Hz."""
        freq = compute_spectral_frequency(17)

        # Should be close to 141.7001 Hz
        self.assertAlmostEqual(freq, 141.7001, delta=0.1,
                              msg="p=17 should produce f₀ ≈ 141.7001 Hz")

    def test_different_primes_different_frequencies(self):
        """Test that different primes produce different frequencies."""
        freq_11 = compute_spectral_frequency(11)
        freq_17 = compute_spectral_frequency(17)
        freq_29 = compute_spectral_frequency(29)

        # All should be different
        self.assertNotEqual(freq_11, freq_17)
        self.assertNotEqual(freq_17, freq_29)
        self.assertNotEqual(freq_11, freq_29)


class TestFrequencyToNote(unittest.TestCase):
    """Test frequency to musical note conversion."""

    def test_frequency_to_note_a440(self):
        """Test that 440 Hz converts to A4."""
        note = frequency_to_note(440.0)
        self.assertEqual(note, "A4")

    def test_frequency_to_note_positive(self):
        """Test frequency conversion for positive frequencies."""
        note = frequency_to_note(141.7)
        self.assertIsInstance(note, str)
        self.assertTrue(len(note) >= 2)  # Should be like "E2"

    def test_frequency_to_note_invalid(self):
        """Test that invalid frequency returns N/A."""
        note = frequency_to_note(0.0)
        self.assertEqual(note, "N/A")

        note = frequency_to_note(-10.0)
        self.assertEqual(note, "N/A")


class TestSpectralMap(unittest.TestCase):
    """Test generation of prime spectral map."""

    def test_generate_spectral_map(self):
        """Test that spectral map is generated correctly."""
        primes = [11, 13, 17, 19, 23, 29]
        spectral_map = generate_prime_spectral_map(primes)

        # Check structure
        self.assertIn('primes', spectral_map)
        self.assertIn('equilibrium_values', spectral_map)
        self.assertIn('frequencies', spectral_map)
        self.assertIn('notes', spectral_map)
        self.assertIn('minimum_prime', spectral_map)
        self.assertIn('resonance_prime', spectral_map)

        # Check lengths match
        self.assertEqual(len(spectral_map['primes']), len(primes))
        self.assertEqual(len(spectral_map['equilibrium_values']), len(primes))
        self.assertEqual(len(spectral_map['frequencies']), len(primes))
        self.assertEqual(len(spectral_map['notes']), len(primes))

    def test_resonance_prime_is_17(self):
        """Test that p=17 is identified as the resonance prime."""
        primes = [11, 13, 17, 19, 23, 29]
        spectral_map = generate_prime_spectral_map(primes)

        # p=17 should be closest to 141.7001 Hz
        self.assertEqual(spectral_map['resonance_prime'], 17,
                        "p=17 should be the resonance prime")

    def test_resonance_frequency_near_141hz(self):
        """Test that resonance frequency is near 141.7 Hz."""
        primes = [11, 13, 17, 19, 23, 29]
        spectral_map = generate_prime_spectral_map(primes)

        resonance_freq = spectral_map['resonance_frequency']
        self.assertAlmostEqual(resonance_freq, 141.7001, delta=0.1,
                              msg="Resonance frequency should be near 141.7 Hz")


class TestP17Verification(unittest.TestCase):
    """Test p=17 resonance verification."""

    def test_verify_p17_resonance(self):
        """Test that p=17 resonance is verified."""
        verification = verify_p17_resonance()

        # Check structure
        self.assertIn('prime', verification)
        self.assertIn('equilibrium', verification)
        self.assertIn('frequency', verification)
        self.assertIn('target_frequency', verification)
        self.assertIn('verified', verification)

        # Check values
        self.assertEqual(verification['prime'], 17)
        self.assertEqual(verification['target_frequency'], 141.7001)

    def test_p17_verification_passes(self):
        """Test that p=17 passes the resonance verification."""
        verification = verify_p17_resonance(tolerance=0.001)

        # Should be verified within tolerance
        self.assertTrue(verification['verified'],
                       "p=17 should pass resonance verification")
        self.assertLess(verification['deviation'], verification['tolerance'])

    def test_p17_frequency_accurate(self):
        """Test that p=17 produces accurate frequency."""
        verification = verify_p17_resonance()

        # Frequency should be very close to 141.7001 Hz
        self.assertAlmostEqual(verification['frequency'], 141.7001, delta=0.001,
                              msg="p=17 frequency should be accurate to 0.001 Hz")


if __name__ == '__main__':
    unittest.main()
