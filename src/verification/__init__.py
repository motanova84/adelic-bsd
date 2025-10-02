"""
Verification Module - Formal BSD proof verification
Implements formal certificate generation and verification
"""

from .formal_bsd_prover import (
    FormalBSDProver,
    generate_formal_certificate
)
from .mass_formal_proof import (
    MassFormalProof,
    batch_prove_bsd
)
from .mass_verification import (
    MassVerification,
    batch_verify_bsd,
    verify_single_curve,
    generate_verification_report
)
from .certificate_generator import (
    CertificateGenerator,
    generate_certificate,
    save_certificate
)
from .selmer_verification import (
    SelmerVerification,
    verify_selmer_maps,
    batch_verify_selmer_maps,
    generate_selmer_verification_report
)

__all__ = [
    'FormalBSDProver',
    'generate_formal_certificate',
    'MassFormalProof',
    'batch_prove_bsd',
    'MassVerification',
    'batch_verify_bsd',
    'verify_single_curve',
    'generate_verification_report',
    'CertificateGenerator',
    'generate_certificate',
    'save_certificate',
    'SelmerVerification',
    'verify_selmer_maps',
    'batch_verify_selmer_maps',
    'generate_selmer_verification_report'
]
