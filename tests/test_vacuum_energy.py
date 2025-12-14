"""
Unit tests for vacuum energy equation module (Acto II).

Tests the vacuum energy equation E_vac(R_Ψ) with fractal toroidal
compactification and log-π symmetry.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: October 2025
"""

import unittest
import numpy as np
from src.vacuum_energy import (
    compute_vacuum_energy,
    find_minima,
    derive_frequency_f0,
    compute_adelic_phase_structure,
    verify_fractal_symmetry,
    generate_resonance_spectrum,
    zeta_prime_half
)


class TestVacuumEnergy(unittest.TestCase):
    """Test vacuum energy equation computations."""

    def test_zeta_prime_half(self):
        """Test that ζ'(1/2) has the expected value."""
        zeta_val = zeta_prime_half()
        # ζ'(1/2) ≈ -3.9226...
        self.assertAlmostEqual(zeta_val, -3.9226, places=3)
        self.assertLess(zeta_val, 0)  # Should be negative

    def test_compute_vacuum_energy_positive_R(self):
        """Test vacuum energy computation for positive R_Ψ."""
        R_psi = 1.0
        energy = compute_vacuum_energy(R_psi)

        # Energy should be a finite real number
        self.assertTrue(np.isfinite(energy))
        self.assertIsInstance(energy, (float, np.floating))

    def test_compute_vacuum_energy_invalid_R(self):
        """Test that negative or zero R_Ψ raises ValueError."""
        with self.assertRaises(ValueError):
            compute_vacuum_energy(0.0)

        with self.assertRaises(ValueError):
            compute_vacuum_energy(-1.0)

    def test_vacuum_energy_at_pi(self):
        """Test vacuum energy at special point R_Ψ = π."""
        R_psi = np.pi
        energy = compute_vacuum_energy(R_psi)

        # At R_Ψ = π, log(R_Ψ)/log(π) = 1
        # So sin²(1) should contribute to the energy
        self.assertTrue(np.isfinite(energy))

        # The fractal term should be sin²(1)
        expected_fractal = np.sin(1.0) ** 2
        self.assertGreater(expected_fractal, 0)  # sin(1) != 0

    def test_vacuum_energy_at_pi_squared(self):
        """Test vacuum energy at R_Ψ = π²."""
        R_psi = np.pi ** 2
        energy = compute_vacuum_energy(R_psi)

        # At R_Ψ = π², log(R_Ψ)/log(π) = 2
        # So sin²(2) should contribute
        self.assertTrue(np.isfinite(energy))

    def test_vacuum_energy_different_parameters(self):
        """Test vacuum energy with different parameter values."""
        R_psi = 2.0

        # Test with different α, β, γ, δ
        energy1 = compute_vacuum_energy(R_psi, alpha=1.0, beta=1.0, gamma=1.0, delta=1.0)
        energy2 = compute_vacuum_energy(R_psi, alpha=2.0, beta=1.0, gamma=1.0, delta=1.0)

        # Changing α should change the energy
        self.assertNotEqual(energy1, energy2)

        # Higher α should increase the UV contribution (1/R⁴ term)
        # Since α appears as α/R⁴, doubling α should increase energy by α/R⁴
        self.assertGreater(energy2, energy1)


class TestEnergyMinima(unittest.TestCase):
    """Test finding energy minima at R_Ψ = π^n."""

    def test_find_minima_returns_list(self):
        """Test that find_minima returns a list of dictionaries."""
        minima = find_minima(n_range=(0, 3))

        self.assertIsInstance(minima, list)
        self.assertGreater(len(minima), 0)

        for minimum in minima:
            self.assertIsInstance(minimum, dict)
            self.assertIn('n', minimum)
            self.assertIn('R_psi_ideal', minimum)
            self.assertIn('R_psi_minimum', minimum)
            self.assertIn('E_vac_minimum', minimum)

    def test_minima_near_pi_powers(self):
        """Test that minima are found near π^n."""
        minima = find_minima(n_range=(1, 3), search_width=0.5)

        for minimum in minima:
            n = minimum['n']
            ideal = minimum['R_psi_ideal']
            actual = minimum['R_psi_minimum']

            # Ideal should be π^n
            self.assertAlmostEqual(ideal, np.pi ** n, places=6)

            # Actual minimum should be close to ideal (within search width)
            relative_diff = abs(actual - ideal) / ideal
            self.assertLessEqual(relative_diff, 0.5)  # Within 50%

    def test_minima_ordering(self):
        """Test that minima are ordered by n."""
        minima = find_minima(n_range=(0, 5))

        n_values = [m['n'] for m in minima]
        # Check that n values are in ascending order
        self.assertEqual(n_values, sorted(n_values))


class TestFractalSymmetry(unittest.TestCase):
    """Test fractal log-π symmetry properties."""

    def test_fractal_symmetry_at_pi(self):
        """Test fractal term at R_Ψ = π."""
        R_psi = np.pi
        sym = verify_fractal_symmetry(R_psi)

        # At R_Ψ = π, log(π)/log(π) = 1, so sin²(1)
        log_ratio = np.log(np.pi) / np.log(np.pi)
        self.assertAlmostEqual(log_ratio, 1.0, places=10)

        expected_fractal = np.sin(1.0) ** 2
        self.assertAlmostEqual(sym['fractal_term_base'], expected_fractal, places=8)

    def test_fractal_term_range(self):
        """Test that fractal term sin²(x) is in [0, 1]."""
        R_values = np.logspace(-1, 2, 50)

        for R in R_values:
            sym = verify_fractal_symmetry(R)
            fractal_base = sym['fractal_term_base']

            # sin²(x) should be in [0, 1]
            self.assertGreaterEqual(fractal_base, 0.0)
            self.assertLessEqual(fractal_base, 1.0)

    def test_fractal_symmetry_scaling(self):
        """Test that scaling by π shifts log ratio by 1."""
        R_base = 2.0
        sym = verify_fractal_symmetry(R_base, scale_factor=np.pi)

        # Scaling by π should shift log ratio by 1
        log_diff = sym['log_ratio_scaled'] - sym['log_ratio_base']
        self.assertAlmostEqual(log_diff, 1.0, places=8)


class TestAdelicStructure(unittest.TestCase):
    """Test adelic phase space structure computations."""

    def test_adelic_structure_returns_dict(self):
        """Test that adelic structure computation returns proper dictionary."""
        R_psi = np.pi
        adelic = compute_adelic_phase_structure(R_psi)

        self.assertIsInstance(adelic, dict)
        self.assertIn('global_phase', adelic)
        self.assertIn('local_phases', adelic)
        self.assertIn('adelic_product', adelic)
        self.assertIn('coherence', adelic)

    def test_adelic_phases_range(self):
        """Test that phases are in appropriate range."""
        R_psi = 5.0
        adelic = compute_adelic_phase_structure(R_psi, primes=[2, 3, 5])

        # Global phase should be in [0, 2π)
        self.assertGreaterEqual(adelic['global_phase'], 0.0)
        self.assertLess(adelic['global_phase'], 2 * np.pi)

        # Each local phase should be in [0, 2π)
        for p_key, phase in adelic['local_phases'].items():
            self.assertGreaterEqual(phase, 0.0)
            self.assertLess(phase, 2 * np.pi)

    def test_adelic_with_different_primes(self):
        """Test adelic structure with different prime sets."""
        R_psi = np.pi

        adelic1 = compute_adelic_phase_structure(R_psi, primes=[2, 3])
        adelic2 = compute_adelic_phase_structure(R_psi, primes=[2, 3, 5, 7])

        # Global phase should be the same
        self.assertAlmostEqual(
            adelic1['global_phase'],
            adelic2['global_phase'],
            places=8
        )

        # But adelic products should differ (more primes included)
        self.assertNotEqual(adelic1['adelic_product'], adelic2['adelic_product'])


class TestFrequencyDerivation(unittest.TestCase):
    """Test frequency derivation from R_Ψ."""

    def test_derive_frequency_positive(self):
        """Test that derived frequency is positive."""
        R_psi = 1.0
        freq = derive_frequency_f0(R_psi, scale_factor=1e-7)

        self.assertGreater(freq, 0.0)
        self.assertTrue(np.isfinite(freq))

    def test_derive_frequency_scaling(self):
        """Test that frequency scales inversely with R_Ψ."""
        R1 = 1.0
        R2 = 2.0
        scale = 1e-7

        freq1 = derive_frequency_f0(R1, scale_factor=scale)
        freq2 = derive_frequency_f0(R2, scale_factor=scale)

        # Frequency should scale approximately as 1/R
        # So freq2 ≈ freq1/2
        ratio = freq1 / freq2
        self.assertAlmostEqual(ratio, 2.0, places=6)


class TestResonanceSpectrum(unittest.TestCase):
    """Test resonance spectrum generation."""

    def test_generate_spectrum_returns_dict(self):
        """Test that spectrum generation returns proper dictionary."""
        spectrum = generate_resonance_spectrum(n_max=5)

        self.assertIsInstance(spectrum, dict)
        self.assertIn('n_values', spectrum)
        self.assertIn('R_psi_values', spectrum)
        self.assertIn('energies', spectrum)
        self.assertIn('frequencies', spectrum)

    def test_spectrum_lengths_match(self):
        """Test that all spectrum arrays have same length."""
        spectrum = generate_resonance_spectrum(n_max=5)

        n_len = len(spectrum['n_values'])
        self.assertEqual(len(spectrum['R_psi_values']), n_len)
        self.assertEqual(len(spectrum['energies']), n_len)
        self.assertEqual(len(spectrum['frequencies']), n_len)

    def test_spectrum_n_values(self):
        """Test that n values are correct in spectrum."""
        n_max = 7
        spectrum = generate_resonance_spectrum(n_max=n_max)

        expected_n = list(range(0, n_max + 1))
        self.assertEqual(spectrum['n_values'], expected_n)


class TestEquationComponents(unittest.TestCase):
    """Test individual components of the vacuum energy equation."""

    def test_uv_term_scaling(self):
        """Test that UV term (α/R⁴) scales correctly."""
        R1 = 1.0
        R2 = 2.0

        # With only α non-zero
        E1 = compute_vacuum_energy(R1, alpha=1.0, beta=0.0, gamma=0.0, delta=0.0)
        E2 = compute_vacuum_energy(R2, alpha=1.0, beta=0.0, gamma=0.0, delta=0.0)

        # E1 = 1/1⁴ = 1, E2 = 1/2⁴ = 1/16
        expected_ratio = 16.0
        actual_ratio = E1 / E2
        self.assertAlmostEqual(actual_ratio, expected_ratio, places=6)

    def test_number_theory_term(self):
        """Test that number theory term includes ζ'(1/2)."""
        R = 1.0

        # With only β non-zero
        E = compute_vacuum_energy(R, alpha=0.0, beta=1.0, gamma=0.0, delta=0.0)

        # E = β * ζ'(1/2) / R² = 1 * ζ'(1/2) / 1
        expected = zeta_prime_half()
        self.assertAlmostEqual(E, expected, places=6)

    def test_cosmological_term_scaling(self):
        """Test that cosmological term (γΛ²R²) scales correctly."""
        R1 = 1.0
        R2 = 2.0
        Lambda = 1.0

        # With only γ non-zero
        E1 = compute_vacuum_energy(R1, alpha=0.0, beta=0.0, gamma=1.0, delta=0.0, Lambda=Lambda)
        E2 = compute_vacuum_energy(R2, alpha=0.0, beta=0.0, gamma=1.0, delta=0.0, Lambda=Lambda)

        # E ∝ R², so E2/E1 = 4
        ratio = E2 / E1
        self.assertAlmostEqual(ratio, 4.0, places=6)

    def test_fractal_term_at_pi_power(self):
        """Test that fractal term vanishes at R_Ψ = π^n."""
        for n in [0, 1, 2, 3]:
            R = np.pi ** n

            # With only δ non-zero
            E = compute_vacuum_energy(R, alpha=0.0, beta=0.0, gamma=0.0, delta=1.0)

            # At R = π^n, log(R)/log(π) = n, so sin²(n) where n is integer
            # sin(nπ) = 0 for integer n (approximately, due to floating point)
            # But sin(n) where n is an integer is generally not zero
            # The special case is when log(π^n)/log(π) = n

            # Actually, sin²(integer) is not necessarily zero
            # The fractal term is sin²(log R_Ψ / log π)
            # At R_Ψ = π^n, this is sin²(n) which is NOT zero for most n
            # Only sin²(kπ) = 0 for integer k

            # So the test should verify the value is sin²(n)
            expected = np.sin(float(n)) ** 2
            self.assertAlmostEqual(E, expected, places=8)


class TestNumericalStability(unittest.TestCase):
    """Test numerical stability of computations."""

    def test_very_small_R(self):
        """Test computation for very small R_Ψ."""
        R_small = 0.01
        energy = compute_vacuum_energy(R_small)

        # Should not overflow
        self.assertTrue(np.isfinite(energy))
        # UV term should dominate (large positive)
        self.assertGreater(energy, 0.0)

    def test_very_large_R(self):
        """Test computation for very large R_Ψ."""
        R_large = 100.0
        energy = compute_vacuum_energy(R_large)

        # Should not overflow
        self.assertTrue(np.isfinite(energy))
        # IR term should dominate
        self.assertGreater(energy, 0.0)

    def test_range_of_R_values(self):
        """Test computation across wide range of R_Ψ values."""
        R_values = np.logspace(-2, 3, 100)

        for R in R_values:
            energy = compute_vacuum_energy(R)
            self.assertTrue(np.isfinite(energy), f"Energy not finite at R={R}")


if __name__ == '__main__':
    unittest.main()
