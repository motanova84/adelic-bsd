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
from .mass_verification import MassBSDVerifier
from .certificate_generator import BSDCertificateGenerator
from .analytical_verification import (
    VerificadorAnalitico,
    FactorLocal,
    demo_verificacion_analitica
)

__all__ = [
    'FormalBSDProver',
    'generate_formal_certificate',
    'MassFormalProof',
    'batch_prove_bsd',
    'MassBSDVerifier',
    'BSDCertificateGenerator',
    'VerificadorAnalitico',
    'FactorLocal',
    'demo_verificacion_analitica'
]
