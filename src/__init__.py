"""
Mota Burruezo Spectral BSD Framework
Spectral finiteness proofs for Tate-Shafarevich groups
"""

from .spectral_finiteness import (
    SpectralFinitenessProver,
    prove_finiteness_for_curve,
    batch_prove_finiteness
)

__version__ = "0.1.0"
__author__ = "Mota Burruezo"

__all__ = [
    "SpectralFinitenessProver",
    "prove_finiteness_for_curve",
    "batch_prove_finiteness"
]
