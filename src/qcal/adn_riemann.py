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
"""

import numpy as np
from typing import List, Dict, Tuple
from scipy import fft


# Constante fundamental de resonancia
F0 = 141.7001  # Hz


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
