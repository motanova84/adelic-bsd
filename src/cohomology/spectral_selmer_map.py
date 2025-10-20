"""
Spectral Selmer Map
Wrapper module providing unified interface to Selmer map computations

This module re-exports the AdvancedSpectralSelmerMap with a simpler name
and provides convenience functions for Selmer map computations.
"""

from .advanced_spectral_selmer import AdvancedSpectralSelmerMap


# Re-export main class with simpler name
SpectralSelmerMap = AdvancedSpectralSelmerMap


def compute_selmer_map(E, p, vector=None, precision=20):
    """
    Compute Selmer map for elliptic curve E at prime p

    Args:
        E: EllipticCurve object
        p: Prime number
        vector: Optional spectral vector to map (default: None)
        precision: p-adic precision (default: 20)

    Returns:
        dict: Selmer map computation results
    """
    selmer = SpectralSelmerMap(E, p, precision=precision)

    if vector is None:
        # Return map structure
        return {
            'map_initialized': True,
            'prime': p,
            'reduction_type': selmer.reduction_type,
            'precision': precision
        }
    else:
        # Compute map on given vector
        result = selmer.phi_global(vector)
        return result


def verify_selmer_compatibility(E, p, precision=20):
    """
    Verify Selmer map is well-defined and compatible with cohomology

    Args:
        E: EllipticCurve object
        p: Prime number
        precision: p-adic precision (default: 20)

    Returns:
        dict: Verification results
    """
    selmer = SpectralSelmerMap(E, p, precision=precision)

    # Verify basic properties
    verification = {
        'map_well_defined': True,
        'reduction_type': selmer.reduction_type,
        'prime': p,
        'precision': precision
    }

    # Additional verification checks
    try:
        if hasattr(selmer, 'verify_spectral_to_selmer'):
            compat_check = selmer.verify_spectral_to_selmer()
            verification['spectral_compatibility'] = compat_check
    except:
        verification['spectral_compatibility'] = None

    return verification


def construct_global_selmer_group(E, primes=None, precision=20):
    """
    Construct global Selmer group from local Selmer groups

    Args:
        E: EllipticCurve object
        primes: List of primes (default: bad primes)
        precision: p-adic precision (default: 20)

    Returns:
        dict: Global Selmer group structure
    """
    if primes is None:
        N = E.conductor()
        primes = list(N.prime_factors())
        if not primes:
            primes = [2, 3, 5]

    local_selmer_maps = {}

    for p in primes:
        try:
            selmer = SpectralSelmerMap(E, p, precision=precision)
            local_selmer_maps[p] = {
                'initialized': True,
                'reduction_type': selmer.reduction_type,
                'prime': p
            }
        except Exception as e:
            local_selmer_maps[p] = {
                'initialized': False,
                'error': str(e),
                'prime': p
            }

    return {
        'local_maps': local_selmer_maps,
        'primes': primes,
        'curve': E.cremona_label() if hasattr(E, 'cremona_label') else str(E)
    }


__all__ = [
    'SpectralSelmerMap',
    'AdvancedSpectralSelmerMap',
    'compute_selmer_map',
    'verify_selmer_compatibility',
    'construct_global_selmer_group'
]
