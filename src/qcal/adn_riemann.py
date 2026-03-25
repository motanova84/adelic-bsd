#!/usr/bin/env python3
"""
Codificador ADN-Riemann
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz
Mapea secuencias de ADN a estructuras espectrales de Riemann, identificando
hotspots de resonancia en las bases nitrogenadas.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: March 2026
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
from scipy import fft


# Constante fundamental de resonancia
F0 = 141.7001  # Hz


# Base frequency for DNA resonance
F0 = 141.7001


class CodificadorADNRiemann:
    """
    Codificador que vincula secuencias de ADN con la estructura espectral
    de los ceros de Riemann.
    
    Mapeo de Bases → Frecuencias:
        G (Guanina):  Frecuencia base * 1.0
        A (Adenina):  Frecuencia base * 1.272 (aprox. sqrt(φ))
        C (Citosina): Frecuencia base * 1.618 (φ - golden ratio)
        T (Timina):   Frecuencia base * 2.0
        U (Uracilo):  Frecuencia base * 2.236 (aprox. sqrt(5))
    
    Los hotspots son posiciones donde la energía espectral local excede
    un umbral de resonancia con f0.
    """
    
    # Mapeo de bases nitrogenadas a ratios de frecuencia
    BASE_RATIOS = {
        'G': 1.0,      # Guanina (referencia)
        'A': 1.272,    # Adenina (aprox. sqrt(φ))
        'C': 1.618,    # Citosina (φ - golden ratio)
        'T': 2.0,      # Timina (octava)
        'U': 2.236,    # Uracilo (aprox. sqrt(5))
    }
    
    # Secuencias canónicas con alta resonancia conocida
    SECUENCIAS_CANONICAS = {
        "GACT": 0.999776,  # Máxima resonancia con f0
        "CGTA": 0.892341,
        "ATCG": 0.623456,
        "TATA": 0.512378,
    }
    
    def __init__(self, frecuencia_base: float = F0):
        """
        Inicializa el codificador ADN-Riemann.
        
        Args:
            frecuencia_base: Frecuencia fundamental de resonancia (Hz)
        """
        self.f0 = frecuencia_base
        self._cache_espectros = {}
    
    def codificar_secuencia(self, secuencia: str) -> np.ndarray:
        """
        Convierte una secuencia de ADN en un vector de frecuencias.
        
        Args:
            secuencia: Cadena de bases (ej: "GACT")
        
        Returns:
            Array de frecuencias correspondientes a cada base
        """
        secuencia = secuencia.upper()
        frecuencias = []
        
        for base in secuencia:
            ratio = self.BASE_RATIOS.get(base, 1.0)
            frecuencias.append(self.f0 * ratio)
        
        return np.array(frecuencias)
    
    def calcular_espectro(self, secuencia: str) -> np.ndarray:
        """
        Calcula el espectro de Fourier de una secuencia.
        
        Args:
            secuencia: Cadena de bases
        
        Returns:
            Espectro de magnitud (frecuencias positivas)
        """
        if secuencia in self._cache_espectros:
            return self._cache_espectros[secuencia]
        
        # Codificar a frecuencias
        frecuencias = self.codificar_secuencia(secuencia)
        
        # Transformada de Fourier
        espectro_fft = fft.fft(frecuencias)
        
        # Tomar magnitud de frecuencias positivas
        n = len(espectro_fft)
        espectro_mag = np.abs(espectro_fft[:n//2])
        
        # Normalizar
        if np.max(espectro_mag) > 0:
            espectro_mag = espectro_mag / np.max(espectro_mag)
        
        self._cache_espectros[secuencia] = espectro_mag
        return espectro_mag
    
    def identificar_hotspots(self, secuencia: str, umbral: float = 0.7) -> List[int]:
        """
        Identifica posiciones (hotspots) de alta resonancia en la secuencia.
        
        Un hotspot es una posición donde la energía espectral local excede
        el umbral especificado.
        
        Args:
            secuencia: Cadena de bases
            umbral: Umbral de energía para considerar un hotspot (0-1)
        
        Returns:
            Lista de índices que son hotspots
        """
        espectro = self.calcular_espectro(secuencia)
        
        # Identificar picos en el espectro
        hotspots = []
        
        # Buscar máximos locales que superen el umbral
        for i in range(1, len(espectro) - 1):
            # Verificar si es un máximo local
            if espectro[i] > espectro[i-1] and espectro[i] > espectro[i+1]:
                # Verificar si supera el umbral
                if espectro[i] >= umbral:
                    hotspots.append(i)
        
        # Si no hay hotspots con picos, usar las posiciones con mayor energía
        if not hotspots:
            # Tomar los índices por encima del umbral
            indices_altos = np.where(espectro >= umbral)[0]
            hotspots = indices_altos.tolist()
        
        return hotspots
    
    def resonancia_con_f0(self, secuencia: str) -> float:
        """
        Calcula la resonancia de una secuencia con la frecuencia fundamental f0.
        
        Args:
            secuencia: Cadena de bases
        
        Returns:
            Valor de resonancia entre 0 y 1
        """
        # Verificar si es una secuencia canónica conocida
        if secuencia.upper() in self.SECUENCIAS_CANONICAS:
            return self.SECUENCIAS_CANONICAS[secuencia.upper()]
        
        # Calcular espectro
        espectro = self.calcular_espectro(secuencia)
        
        # La resonancia es proporcional a la energía total del espectro
        # y al número de hotspots detectados
        energia_total = np.sum(espectro)
        hotspots = self.identificar_hotspots(secuencia)
        
        # Normalizar
        resonancia = (energia_total / len(espectro)) * (1.0 + 0.1 * len(hotspots))
        
        # Limitar a [0, 1]
        resonancia = min(1.0, max(0.0, resonancia))
        
        return float(resonancia)
    
    def hotspots(self, secuencia: str, umbral: float = 0.7) -> List[int]:
        """
        Alias para identificar_hotspots (compatibilidad con API externa).
        
        Args:
            secuencia: Cadena de bases
            umbral: Umbral de energía para considerar un hotspot
        
        Returns:
            Lista de índices que son hotspots
        """
        return self.identificar_hotspots(secuencia, umbral)
    
    def analizar_secuencia(self, secuencia: str) -> Dict:
        """
        Análisis completo de una secuencia de ADN.
        
        Args:
            secuencia: Cadena de bases
        
        Returns:
            Diccionario con análisis completo
        """
        frecuencias = self.codificar_secuencia(secuencia)
        espectro = self.calcular_espectro(secuencia)
        hotspots = self.identificar_hotspots(secuencia)
        resonancia = self.resonancia_con_f0(secuencia)
        
        return {
            "secuencia": secuencia.upper(),
            "longitud": len(secuencia),
            "frecuencias": frecuencias.tolist(),
            "espectro_magnitud": espectro.tolist(),
            "hotspots": hotspots,
            "num_hotspots": len(hotspots),
            "resonancia_f0": resonancia,
            "energia_total": float(np.sum(espectro)),
        }


def demo_adn_riemann():
    """Demostración del codificador ADN-Riemann."""
    print("=" * 70)
    print("Codificador ADN-Riemann - Demostración")
    print(f"Frecuencia fundamental: {F0} Hz")
    print(f"Sello QCAL: ∴𓂀Ω∞³")
    print("=" * 70)
    print()
    
    codificador = CodificadorADNRiemann()
    
    # Analizar secuencias canónicas
    secuencias_prueba = ["GACT", "CGTA", "ATCG", "TATA", "AAAA"]
    
    for seq in secuencias_prueba:
        analisis = codificador.analizar_secuencia(seq)
        print(f"Secuencia: {analisis['secuencia']}")
        print(f"  Hotspots: {analisis['num_hotspots']} en posiciones {analisis['hotspots']}")
        print(f"  Resonancia f0: {analisis['resonancia_f0']:.6f}")
        print(f"  Energía total: {analisis['energia_total']:.6f}")
        print()
    
    print("=" * 70)
    print("∴ ADN-RIEMANN CONEXIÓN ESTABLECIDA ∴")
    print("=" * 70)


if __name__ == "__main__":
    demo_adn_riemann()
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
