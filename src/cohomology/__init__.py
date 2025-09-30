"""
Cohomology Module - p-adic cohomology and Selmer structures
Implements advanced cohomology theory for BSD framework
"""

from .advanced_spectral_selmer import AdvancedSpectralSelmerMap
from .spectral_selmer_map import (
    SpectralSelmerMap,
    compute_selmer_map,
    verify_selmer_compatibility,
    construct_global_selmer_group
)
from .p_adic_integration import (
    PAdicIntegration,
    compute_p_adic_height
)
from .bloch_kato_conditions import (
    BlochKatoConditions,
    verify_bloch_kato
)

__all__ = [
    'AdvancedSpectralSelmerMap',
    'SpectralSelmerMap',
    'compute_selmer_map',
    'verify_selmer_compatibility',
    'construct_global_selmer_group',
    'PAdicIntegration',
    'compute_p_adic_height',
    'BlochKatoConditions',
    'verify_bloch_kato'
]
