"""
Heights Module - Advanced height pairing theory
Implements Beilinson-Bloch height theory for BSD framework
"""

from .advanced_spectral_heights import (
    AdvancedSpectralHeightPairing,
    verify_height_equality,
    compute_regulator_comparison
)

from .height_comparison import (
    HeightComparison,
    compare_heights,
    verify_regulator_compatibility
)

__all__ = [
    'AdvancedSpectralHeightPairing',
    'verify_height_equality',
    'compute_regulator_comparison',
    'HeightComparison',
    'compare_heights',
    'verify_regulator_compatibility'
]
