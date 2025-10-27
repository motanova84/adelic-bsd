"""
BSD Spectral Framework Package
===============================

A SageMath-compatible package for verifying the Birch-Swinnerton-Dyer conjecture
via spectral methods and adelic operators.

Modules:
--------
- finiteness: Spectral finiteness proofs for Tate-Shafarevich groups
- selmer: Advanced Selmer map verification with p-adic cohomology
- heights: Beilinson-Bloch height pairings and regulators
- vacuum_energy: Fractal toroidal compactification and adelic phase structure

Examples:
---------
>>> from bsd_spectral import prove_finiteness
>>> result = prove_finiteness('11a1')
>>> print(f"Finiteness proved: {result['finiteness_proved']}")

>>> from bsd_spectral import verify_selmer_maps
>>> cert = verify_selmer_maps('37a1', primes=[2, 3])
>>> print(f"Selmer verification: {cert['verification_passed']}")

>>> from bsd_spectral import compute_beilinson_bloch_regulator
>>> reg = compute_beilinson_bloch_regulator('389a1')
>>> print(f"Regulator: {reg}")

Version: 0.3.0
Author: Mota Burruezo
License: MIT
"""

__version__ = '0.3.0'
__author__ = 'Mota Burruezo'
__license__ = 'MIT'

# Import vacuum energy (no SageMath required)
from .vacuum_energy import (
    compute_vacuum_energy,
    find_minima,
    derive_frequency_f0,
    compute_adelic_phase_structure,
    verify_fractal_symmetry,
    generate_resonance_spectrum
)

# Try to import SageMath-dependent modules
try:
    from .finiteness import (
        prove_finiteness,
        batch_prove_finiteness,
        generate_finiteness_certificate
    )
    _SAGE_AVAILABLE = True
except ImportError:
    _SAGE_AVAILABLE = False
    prove_finiteness = None
    batch_prove_finiteness = None
    generate_finiteness_certificate = None

try:
    from .selmer import (
        verify_selmer_maps,
        batch_verify_selmer_maps,
        generate_selmer_certificate
    )
except ImportError:
    verify_selmer_maps = None
    batch_verify_selmer_maps = None
    generate_selmer_certificate = None

try:
    from .heights import (
        compute_beilinson_bloch_regulator,
        verify_height_compatibility,
        batch_verify_heights,
        generate_height_certificate
    )
except ImportError:
    compute_beilinson_bloch_regulator = None
    verify_height_compatibility = None
    batch_verify_heights = None
    generate_height_certificate = None

__all__ = [
    # Version info
    '__version__',
    '__author__',
    '__license__',
    
    # Vacuum energy (always available)
    'compute_vacuum_energy',
    'find_minima',
    'derive_frequency_f0',
    'compute_adelic_phase_structure',
    'verify_fractal_symmetry',
    'generate_resonance_spectrum',
    
    # Finiteness (requires SageMath)
    'prove_finiteness',
    'batch_prove_finiteness',
    'generate_finiteness_certificate',
    
    # Selmer (requires SageMath)
    'verify_selmer_maps',
    'batch_verify_selmer_maps',
    'generate_selmer_certificate',
    
    # Heights (requires SageMath)
    'compute_beilinson_bloch_regulator',
    'verify_height_compatibility',
    'batch_verify_heights',
    'generate_height_certificate',
]


def check_sage_availability():
    """
    Check if SageMath is available.
    
    Returns:
        bool: True if SageMath modules can be imported
    """
    return _SAGE_AVAILABLE


def get_version_info():
    """
    Get detailed version information.
    
    Returns:
        dict: Version info including dependencies
    """
    info = {
        'version': __version__,
        'author': __author__,
        'license': __license__,
        'sage_available': _SAGE_AVAILABLE
    }
    
    try:
        import numpy
        info['numpy_version'] = numpy.__version__
    except ImportError:
        info['numpy_version'] = 'not installed'
    
    try:
        import scipy
        info['scipy_version'] = scipy.__version__
    except ImportError:
        info['scipy_version'] = 'not installed'
    
    return info
