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

# Import SABIO Infinity4 module (no SageMath dependency)
from .sabio_infinity4 import (
    SABIO_Infinity4,
    ResonanciaQuantica,
    MatrizSimbiosis,
    crear_sistema_sabio,
    validacion_rapida
)

# Import BSD ∞³ Theorem module (no SageMath dependency)
from .bsd_infinity3_theorem import (
    BSDInfinity3Theorem,
    BSDInfinity3Certificate,
    SpectralFrequencyResult,
    compute_spectral_frequency,
    compute_fundamental_constants,
    verify_golden_ratio_identity,
    verify_phi_cube_formula,
    demonstrate_bsd_infinity3
)

# Import cryptographic validation module (no SageMath dependency)
from .crypto_validation import (
    CryptoValidator,
    EdDSAValidator,
    validate_elliptic_curve_for_crypto
)

# Import post-quantum blockchain module (no SageMath dependency)
from .postquantum_blockchain import (
    PostQuantumSignature,
    Transaction,
    Block,
    PostQuantumBlockchain,
    create_secure_transaction,
    verify_transaction_chain
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
    from .dR_compatibility import (
        compute_h1f_dimension,
        compute_dR_dimension,
        verify_dR_compatibility
    )
except ImportError:
    compute_h1f_dimension = None
    compute_dR_dimension = None
    verify_dR_compatibility = None

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

try:
    from .PT_compatibility import (
        PTCompatibilityProver,
        prove_PT_all_ranks
    )
except ImportError:
    PTCompatibilityProver = None
    prove_PT_all_ranks = None

try:
    from .central_identity import (
        CentralIdentity,
        demonstrate_central_identity
    )
except ImportError:
    CentralIdentity = None
    demonstrate_central_identity = None

__version__ = "0.2.2"
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
    # SABIO Infinity4 module (new in v0.2.3)
    "SABIO_Infinity4",
    "ResonanciaQuantica",
    "MatrizSimbiosis",
    "crear_sistema_sabio",
    "validacion_rapida",
    # Cryptographic validation module (new)
    "CryptoValidator",
    "EdDSAValidator",
    "validate_elliptic_curve_for_crypto",
    # Post-quantum blockchain module (new)
    "PostQuantumSignature",
    "Transaction",
    "Block",
    "PostQuantumBlockchain",
    "create_secure_transaction",
    "verify_transaction_chain",
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
    "CertificateGenerator",
    # dR compatibility module
    "compute_h1f_dimension",
    "compute_dR_dimension",
    "verify_dR_compatibility",
    # PT Compatibility
    "PTCompatibilityProver",
    "prove_PT_all_ranks",
    # Central Identity (new in v0.2.2)
    "CentralIdentity",
    "demonstrate_central_identity",
    # BSD ∞³ Theorem (new in v0.2.3)
    "BSDInfinity3Theorem",
    "BSDInfinity3Certificate",
    "SpectralFrequencyResult",
    "compute_spectral_frequency",
    "compute_fundamental_constants",
    "verify_golden_ratio_identity",
    "verify_phi_cube_formula",
    "demonstrate_bsd_infinity3"
]
