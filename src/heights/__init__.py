"""
Heights Module - Advanced height pairing theory
Implements Beilinson-Bloch height theory for BSD framework
"""

from .advanced_spectral_heights import (
    AdvancedSpectralHeightPairing,
    verify_height_equality,
    compute_regulator_comparison
)

__all__ = [
    'AdvancedSpectralHeightPairing',
    'verify_height_equality',
    'compute_regulator_comparison'
]
