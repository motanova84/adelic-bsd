"""
Spectral Finiteness Framework - Mota Burruezo
==============================================

Main package for spectral methods for proving finiteness of Tate-Shafarevich groups.

Modules:
--------
- spectral_finiteness: Main interface and orchestration
- spectral_operator: Spectral operator construction M_E,p(s)
- kernel_computation: Kernel dimension and lattice analysis
- global_bound: Global bound computation on #Ш
- certificate_generator: Certificate generation in multiple formats
"""

from .spectral_finiteness import (
    SpectralFinitenessProver,
    prove_finiteness_for_curve,
    batch_prove_finiteness
)

from .spectral_operator import (
    SpectralOperatorBuilder,
    construct_spectral_operator
)

from .kernel_computation import (
    KernelAnalyzer,
    SpectralSelmerAnalyzer,
    compute_kernel_dimension,
    compute_kernel_basis
)

from .global_bound import (
    GlobalBoundComputer,
    BoundVerifier,
    compute_global_bound,
    compute_local_bound
)

from .certificate_generator import (
    CertificateGenerator,
    FinitenessCache,
    generate_certificate
)

__all__ = [
    # Main interface
    'SpectralFinitenessProver',
    'prove_finiteness_for_curve',
    'batch_prove_finiteness',
    
    # Operator construction
    'SpectralOperatorBuilder',
    'construct_spectral_operator',
    
    # Kernel computation
    'KernelAnalyzer',
    'SpectralSelmerAnalyzer',
    'compute_kernel_dimension',
    'compute_kernel_basis',
    
    # Global bounds
    'GlobalBoundComputer',
    'BoundVerifier',
    'compute_global_bound',
    'compute_local_bound',
    
    # Certificates
    'CertificateGenerator',
    'FinitenessCache',
    'generate_certificate',
]
