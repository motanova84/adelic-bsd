#!/usr/bin/env python3
"""
ADN-Riemann Codifier — Biological Quantum Resonance
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Maps DNA sequences (GACT) to Riemann spectral structure.
Identifies resonant hotspots that align with f₀ frequency.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
"""

import numpy as np
from typing import List, Dict, Tuple


# Base frequency for DNA resonance
F0 = 141.7001


class CodificadorADNRiemann:
    """
    DNA-Riemann Codifier for quantum resonance mapping.
    
    Maps DNA base sequences to spectral frequencies and identifies
    hotspots where the sequence resonates with f₀.
    """
    
    # Frequency mapping for DNA bases (in arbitrary units aligned with f₀)
    BASE_FREQUENCIES = {
        'G': 1.0,   # Guanine
        'A': 2.0,   # Adenine
        'C': 3.0,   # Cytosine
        'T': 4.0,   # Timina
    }
    
    def __init__(self, f0: float = F0):
        """
        Initialize the DNA-Riemann codifier.
        
        Args:
            f0: Base resonance frequency (default: 141.7001 Hz)
        """
        self.f0 = f0
        self.coherencia_umbral = 0.888  # Minimum coherence threshold
    
    def codificar_secuencia(self, secuencia: str) -> np.ndarray:
        """
        Encode a DNA sequence into a frequency array.
        
        Args:
            secuencia: DNA sequence string (e.g., "GACT")
            
        Returns:
            Array of frequencies corresponding to each base
        """
        secuencia_upper = secuencia.upper()
        return np.array([
            self.BASE_FREQUENCIES.get(base, 0.0) 
            for base in secuencia_upper
        ])
    
    def calcular_resonancia(self, secuencia: str) -> float:
        """
        Calculate resonance coefficient of a DNA sequence with f₀.
        
        Args:
            secuencia: DNA sequence string
            
        Returns:
            Resonance coefficient [0, 1], where 1 is perfect resonance
        """
        if not secuencia:
            return 0.0
        
        # Encode sequence
        freqs = self.codificar_secuencia(secuencia)
        
        # Calculate harmonic mean relative to f₀ pattern
        # GACT has maximum resonance (pattern: 1,2,3,4)
        patron_optimo = np.array([1.0, 2.0, 3.0, 4.0])
        
        # Normalize to same length
        if len(freqs) >= len(patron_optimo):
            patron = np.tile(patron_optimo, len(freqs) // len(patron_optimo) + 1)[:len(freqs)]
        else:
            patron = patron_optimo[:len(freqs)]
        
        # Calculate correlation
        if len(freqs) > 0 and np.std(freqs) > 0 and np.std(patron) > 0:
            correlacion = np.corrcoef(freqs, patron)[0, 1]
            # Transform to [0, 1] range
            resonancia = (correlacion + 1.0) / 2.0
        else:
            resonancia = 0.5
        
        return float(resonancia)
    
    def identificar_hotspots(self, secuencia: str, ventana: int = 4) -> List[Dict]:
        """
        Identify resonant hotspots in a DNA sequence.
        
        A hotspot is a subsequence with high resonance with f₀.
        
        Args:
            secuencia: DNA sequence string
            ventana: Window size for sliding analysis (default: 4 for GACT)
            
        Returns:
            List of hotspot dictionaries with position, sequence, and resonance
        """
        if len(secuencia) < ventana:
            return []
        
        hotspots = []
        secuencia_upper = secuencia.upper()
        
        # Sliding window analysis
        for i in range(len(secuencia_upper) - ventana + 1):
            subsec = secuencia_upper[i:i+ventana]
            resonancia = self.calcular_resonancia(subsec)
            
            # If resonance exceeds threshold, it's a hotspot
            if resonancia >= self.coherencia_umbral:
                hotspots.append({
                    'posicion': i,
                    'secuencia': subsec,
                    'resonancia': resonancia,
                    'frecuencia_base': self.f0
                })
        
        # Sort by resonance (descending)
        hotspots.sort(key=lambda x: x['resonancia'], reverse=True)
        
        return hotspots
    
    def es_secuencia_logos(self, secuencia: str) -> bool:
        """
        Check if a sequence is a Logos sequence (GACT or high resonance).
        
        Args:
            secuencia: DNA sequence string
            
        Returns:
            True if sequence has Logos-level resonance (≥ 0.999)
        """
        if secuencia.upper() == "GACT":
            return True
        
        resonancia = self.calcular_resonancia(secuencia)
        return resonancia >= 0.999


# Module-level convenience function
def identificar_hotspots_adn(secuencia: str, f0: float = F0) -> List[Dict]:
    """
    Convenience function to identify DNA hotspots.
    
    Args:
        secuencia: DNA sequence string
        f0: Base resonance frequency
        
    Returns:
        List of hotspot dictionaries
    """
    codificador = CodificadorADNRiemann(f0=f0)
    return codificador.identificar_hotspots(secuencia)


if __name__ == "__main__":
    # Demo
    codif = CodificadorADNRiemann()
    
    print("=== DNA-Riemann Codifier Demo ===")
    print(f"f₀ = {codif.f0} Hz\n")
    
    # Test GACT (optimal sequence)
    secuencia_test = "GACT"
    resonancia = codif.calcular_resonancia(secuencia_test)
    print(f"Secuencia: {secuencia_test}")
    print(f"Resonancia: {resonancia:.6f}")
    print(f"Es Logos: {codif.es_secuencia_logos(secuencia_test)}\n")
    
    # Test larger sequence
    secuencia_grande = "GACTGACTAAATTTCCCGGG"
    hotspots = codif.identificar_hotspots(secuencia_grande)
    print(f"Secuencia: {secuencia_grande}")
    print(f"Hotspots encontrados: {len(hotspots)}")
    for hs in hotspots[:3]:  # Show top 3
        print(f"  Pos {hs['posicion']}: {hs['secuencia']} (resonancia={hs['resonancia']:.3f})")
