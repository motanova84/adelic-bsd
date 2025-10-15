"""
Mota Burruezo Spectral BSD Framework
Spectral finiteness proofs for Tate-Shafarevich groups
"""

# Import vacuum energy module (no SageMath dependency)
from .vacuum_energy import (
    compute_vacuum_energy,
    find_minima,
    derive_frequency_f0,
    compute_adelic_phase_structure,
    verify_fractal_symmetry,
    generate_resonance_spectrum,
    zeta_prime_half
)

# Try to import SageMath-dependent modules
try:
    from .spectral_finiteness import (
        SpectralFinitenessProver,
        prove_finiteness_for_curve,
        batch_prove_finiteness
    )
    _SAGE_AVAILABLE = True
except ImportError:
    _SAGE_AVAILABLE = False
    SpectralFinitenessProver = None
    prove_finiteness_for_curve = None
    batch_prove_finiteness = None

try:
    from .spectral_cycles import (
        SpectralCycleConstructor,
        spectral_kernel_to_rational_points,
        compute_kernel_basis,
        demonstrate_spectral_to_points
    )
except ImportError:
    SpectralCycleConstructor = None
    spectral_kernel_to_rational_points = None
    compute_kernel_basis = None
    demonstrate_spectral_to_points = None

try:
    from .height_pairing import (
        compute_spectral_height_matrix,
        compute_nt_height_matrix,
        verify_height_compatibility,
        batch_verify_height_compatibility
    )
except ImportError:
    compute_spectral_height_matrix = None
    compute_nt_height_matrix = None
    verify_height_compatibility = None
    batch_verify_height_compatibility = None

try:
    from .lmfdb_verification import (
        large_scale_verification,
        generate_verification_report,
        get_lmfdb_curves
    )
except ImportError:
    large_scale_verification = None
    generate_verification_report = None
    get_lmfdb_curves = None

# Core modules
try:
    from .adelic_operator import AdelicOperator
    from .local_factors import LocalFactors
    from .spectral_bsd import SpectralBSD
except ImportError:
    AdelicOperator = None
    LocalFactors = None
    SpectralBSD = None

# Advanced modules
try:
    from .cohomology import (
        AdvancedSpectralSelmerMap,
        SpectralSelmerMap,
        PAdicIntegration,
        BlochKatoConditions
    )
except ImportError:
    AdvancedSpectralSelmerMap = None
    SpectralSelmerMap = None
    PAdicIntegration = None
    BlochKatoConditions = None

try:
    from .heights import (
        AdvancedSpectralHeightPairing,
        HeightComparison,
        verify_height_equality,
        compute_regulator_comparison
    )
except ImportError:
    AdvancedSpectralHeightPairing = None
    HeightComparison = None
    verify_height_equality = None
    compute_regulator_comparison = None

try:
    from .verification import (
        FormalBSDProver,
        generate_formal_certificate,
        MassFormalProof,
        MassVerification,
        batch_prove_bsd,
        CertificateGenerator
    )
except ImportError:
    FormalBSDProver = None
    generate_formal_certificate = None
    MassFormalProof = None
    MassVerification = None
    batch_prove_bsd = None
    CertificateGenerator = None

__version__ = "0.2.1"
__author__ = "Mota Burruezo"

__all__ = [
    # Vacuum energy module (new in v0.2.1)
    "compute_vacuum_energy",
    "find_minima",
    "derive_frequency_f0",
    "compute_adelic_phase_structure",
    "verify_fractal_symmetry",
    "generate_resonance_spectrum",
    "zeta_prime_half",
    # Spectral finiteness (SageMath required)
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
    "get_lmfdb_curves",
    # Core modules
    "AdelicOperator",
    "LocalFactors",
    "SpectralBSD",
    # Advanced modules
    "AdvancedSpectralSelmerMap",
    "SpectralSelmerMap",
    "PAdicIntegration",
    "BlochKatoConditions",
    "AdvancedSpectralHeightPairing",
    "HeightComparison",
    "verify_height_equality",
    "compute_regulator_comparison",
    "FormalBSDProver",
    "generate_formal_certificate",
    "MassFormalProof",
    "MassVerification",
    "batch_prove_bsd",
    "CertificateGenerator"
]
