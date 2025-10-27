"""
Vacuum Energy Module
====================

Fractal toroidal compactification and adelic phase structure.

This module implements the vacuum energy equation with log-π symmetry
and connection to the adelic phase space structure.
"""

import sys
import os

# Import from src
try:
    from ..src.vacuum_energy import *
except (ImportError, ValueError):
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from src.vacuum_energy import *

# Re-export all functions
__all__ = [
    'compute_vacuum_energy',
    'find_minima',
    'derive_frequency_f0',
    'compute_adelic_phase_structure',
    'verify_fractal_symmetry',
    'generate_resonance_spectrum',
    'zeta_prime_half'
]
