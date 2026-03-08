"""
QCAL (Quantum Consciousness Artificial Logos) - Module Package
================================================================

Unification framework for the Millennium Problems through spectral operators
and universal constants.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Frequency: 141.7001 Hz (Universal Noetic Resonance)
Seal: ∴𓂀Ω∞³

Modules:
    - adn_riemann: ADN-Riemann encoder for biological-mathematical mapping
    - bsd_adelic_connector: BSD Adélico connector - Pentagon Logos closure
    - integrate_qcal_compact: Integration script for full system validation
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo (JMMB Ψ·∴)"
__frequency__ = 141.7001  # Hz - Universal Noetic Resonance
__seal__ = "∴𓂀Ω∞³"

from .adn_riemann import CodificadorADNRiemann
from .bsd_adelic_connector import sincronizar_bsd_adn

__all__ = [
    "CodificadorADNRiemann",
    "sincronizar_bsd_adn",
]
