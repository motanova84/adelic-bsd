"""
Mota Burruezo Spectral BSD Framework
Spectral finiteness proofs for Tate-Shafarevich groups
"""

from .spectral_finiteness import (
    SpectralFinitenessProver,
    prove_finiteness_for_curve,
    batch_prove_finiteness
)

from .spectral_cycles import (
    SpectralCycleConstructor,
    spectral_kernel_to_rational_points,
    compute_kernel_basis,
    demonstrate_spectral_to_points
)

from .height_pairing import (
    compute_spectral_height_matrix,
    compute_nt_height_matrix,
    verify_height_compatibility,
    batch_verify_height_compatibility
)

from .lmfdb_verification import (
    large_scale_verification,
    generate_verification_report,
    get_lmfdb_curves
)

__version__ = "0.1.0"
__author__ = "Mota Burruezo"

__all__ = [
    "SpectralFinitenessProver",
    "prove_finiteness_for_curve",
    "batch_prove_finiteness",
    "SpectralCycleConstructor",
    "spectral_kernel_to_rational_points",
    "compute_kernel_basis",
    "demonstrate_spectral_to_points",
    "compute_spectral_height_matrix",
    "compute_nt_height_matrix",
    "verify_height_compatibility",
    "batch_verify_height_compatibility",
    "large_scale_verification",
    "generate_verification_report",
    "get_lmfdb_curves"
]
