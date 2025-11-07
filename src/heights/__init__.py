"""
Heights Module - Advanced height pairing theory
Implements Beilinson-Bloch height theory for BSD framework
"""

from .advanced_spectral_heights import (
    AdvancedSpectralHeightPairing,
    verify_height_equality as verify_height_equality_advanced,
    compute_regulator_comparison as compute_regulator_comparison_advanced
)
from .height_comparison import (
    HeightComparator,
    verify_height_equality
)

from .height_comparison import (
    HeightComparison,
    compare_heights,
    verify_regulator_compatibility
)

__all__ = [
    'AdvancedSpectralHeightPairing',
    'HeightComparator',
    'verify_height_equality',
    'verify_height_equality_advanced',
    'compute_regulator_comparison_advanced'
]
