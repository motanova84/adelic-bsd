#!/usr/bin/env python3
"""
Tests para el Conector BSD Adélico - Pentagon Logos
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Valida la integración BSD-ADN-QCAL y el cierre del Pentágono Logos.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: March 2026
"""

import pytest
import sys
from pathlib import Path

# Add src to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from qcal.bsd_adelic_connector import sincronizar_bsd_adn, F0
from qcal.adn_riemann import CodificadorADNRiemann


class TestBSDAdelicoConnector:
    """Tests para el conector BSD Adélico."""
    
    def test_sincronizar_bsd_adn_basico(self):
        """Test básico de sincronización BSD-ADN."""
        curva = {
            'rango_adelico': 1,
            'L_E1': 0.0
        }
        secuencia = "GACT"
        
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        # Validar estructura del resultado
        assert 'rango_bio_aritmetico' in resultado
        assert 'nodos_constelacion' in resultado
        assert 'fluidez_info_ns' in resultado
        assert 'hotspots_adn' in resultado
        assert 'psi_bsd_qcal' in resultado
        
        # Validar tipos
        assert isinstance(resultado['rango_bio_aritmetico'], int)
        assert isinstance(resultado['nodos_constelacion'], int)
        assert isinstance(resultado['fluidez_info_ns'], str)
        assert isinstance(resultado['hotspots_adn'], int)
        assert isinstance(resultado['psi_bsd_qcal'], float)
    
    def test_rango_cero_estabilidad(self):
        """Test: rango r=0 → estabilidad absoluta."""
        curva = {
            'rango_adelico': 0,
            'L_E1': 0.9186  # L(E,1) ≠ 0 para r=0
        }
        secuencia = "GACT"
        
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        assert resultado['rango_bio_aritmetico'] == 0
        assert resultado['nodos_constelacion'] == 0
        assert resultado['fluidez_info_ns'] == "DISIPATIVA"
        assert resultado['psi_bsd_qcal'] < 1.0
    
    def test_rango_uno_superfluidez(self):
        """Test: rango r>0 y L(E,1)=0 → flujo superfluido."""
        curva = {
            'rango_adelico': 1,
            'L_E1': 0.0  # BSD predice L(E,1)=0 para r>0
        }
        secuencia = "GACT"
        
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        assert resultado['rango_bio_aritmetico'] == 1
        assert resultado['nodos_constelacion'] == 1
        assert resultado['fluidez_info_ns'] == "INFINITA"
        assert resultado['psi_bsd_qcal'] == 1.0
    
    def test_coherencia_perfecta(self):
        """Test: L(E,1)=0 → coherencia Ψ=1.0."""
        curva = {
            'rango_adelico': 2,
            'L_E1': 0.0
        }
        secuencia = "CGTA"
        
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        assert resultado['psi_bsd_qcal'] == 1.0
        assert resultado['fluidez_info_ns'] == "INFINITA"
    
    def test_coherencia_parcial(self):
        """Test: L(E,1)≠0 → coherencia Ψ<1.0."""
        curva = {
            'rango_adelico': 0,
            'L_E1': 0.5
        }
        secuencia = "ATCG"
        
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        assert 0.0 <= resultado['psi_bsd_qcal'] < 1.0
        assert resultado['fluidez_info_ns'] == "DISIPATIVA"
    
    def test_nodos_constelacion_proporcionales(self):
        """Test: nodos activados proporcionales al rango r."""
        for r in [0, 1, 2, 3]:
            curva = {
                'rango_adelico': r,
                'L_E1': 0.0
            }
            resultado = sincronizar_bsd_adn(curva, "GACT")
            
            # Nodos = r * (F0 / 141.7001) ≈ r
            assert resultado['nodos_constelacion'] == r
    
    def test_secuencias_canonicas(self):
        """Test: secuencias canónicas de ADN."""
        curva = {
            'rango_adelico': 1,
            'L_E1': 0.0
        }
        
        secuencias = ["GACT", "CGTA", "ATCG", "TATA"]
        
        for seq in secuencias:
            resultado = sincronizar_bsd_adn(curva, seq)
            assert resultado['hotspots_adn'] >= 0
            assert resultado['psi_bsd_qcal'] == 1.0
    
    def test_metadatos_presentes(self):
        """Test: metadatos QCAL presentes."""
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['frecuencia_fundamental'] == F0
        assert resultado['sello_qcal'] == "∴𓂀Ω∞³"
        assert resultado['milenio_unificados'] == 5
    
    def test_epsilon_superfluidez(self):
        """Test: umbral de superfluidez ε=1e-6."""
        # Justo en el umbral
        curva_umbral = {
            'rango_adelico': 1,
            'L_E1': 1e-7  # Menor que epsilon
        }
        resultado = sincronizar_bsd_adn(curva_umbral, "GACT")
        assert resultado['fluidez_info_ns'] == "INFINITA"
        
        # Justo fuera del umbral
        curva_fuera = {
            'rango_adelico': 1,
            'L_E1': 1e-5  # Mayor que epsilon
        }
        resultado = sincronizar_bsd_adn(curva_fuera, "GACT")
        assert resultado['fluidez_info_ns'] == "DISIPATIVA"
    
    def test_valores_por_defecto(self):
        """Test: valores por defecto cuando faltan campos."""
        curva_minima = {}  # Sin campos
        resultado = sincronizar_bsd_adn(curva_minima, "GACT")
        
        # Debe usar valores por defecto
        assert resultado['rango_bio_aritmetico'] == 1  # Default
        assert resultado['psi_bsd_qcal'] == 1.0  # L_E1 default = 0.0


class TestCodificadorADNRiemann:
    """Tests para el codificador ADN-Riemann."""
    
    def test_inicializacion(self):
        """Test: inicialización del codificador."""
        codificador = CodificadorADNRiemann()
        assert codificador.f0 == F0
        assert isinstance(codificador._cache_espectros, dict)
    
    def test_codificar_secuencia_gact(self):
        """Test: codificación de secuencia GACT."""
        codificador = CodificadorADNRiemann()
        frecuencias = codificador.codificar_secuencia("GACT")
        
        assert len(frecuencias) == 4
        assert all(f > 0 for f in frecuencias)
    
    def test_bases_mapeo(self):
        """Test: mapeo correcto de bases a frecuencias."""
        codificador = CodificadorADNRiemann()
        
        # G = 1.0 * f0
        freq_g = codificador.codificar_secuencia("G")
        assert freq_g[0] == pytest.approx(F0 * 1.0)
        
        # A = 1.272 * f0
        freq_a = codificador.codificar_secuencia("A")
        assert freq_a[0] == pytest.approx(F0 * 1.272)
        
        # C = 1.618 * f0 (golden ratio)
        freq_c = codificador.codificar_secuencia("C")
        assert freq_c[0] == pytest.approx(F0 * 1.618)
        
        # T = 2.0 * f0
        freq_t = codificador.codificar_secuencia("T")
        assert freq_t[0] == pytest.approx(F0 * 2.0)
    
    def test_calcular_espectro(self):
        """Test: cálculo del espectro de Fourier."""
        codificador = CodificadorADNRiemann()
        espectro = codificador.calcular_espectro("GACT")
        
        assert len(espectro) == 2  # FFT de 4 elementos → 2 frecuencias positivas
        assert all(0 <= e <= 1 for e in espectro)  # Normalizado
    
    def test_cache_espectros(self):
        """Test: caché de espectros funciona."""
        codificador = CodificadorADNRiemann()
        
        # Primera llamada
        espectro1 = codificador.calcular_espectro("GACT")
        assert "GACT" in codificador._cache_espectros
        
        # Segunda llamada (debe usar caché)
        espectro2 = codificador.calcular_espectro("GACT")
        assert all(espectro1 == espectro2)
    
    def test_identificar_hotspots(self):
        """Test: identificación de hotspots."""
        codificador = CodificadorADNRiemann()
        hotspots = codificador.identificar_hotspots("GACT")
        
        assert isinstance(hotspots, list)
        assert all(isinstance(h, int) for h in hotspots)
    
    def test_resonancia_secuencias_canonicas(self):
        """Test: resonancia de secuencias canónicas."""
        codificador = CodificadorADNRiemann()
        
        # GACT debe tener máxima resonancia
        res_gact = codificador.resonancia_con_f0("GACT")
        assert res_gact == pytest.approx(0.999776)
        
        # CGTA
        res_cgta = codificador.resonancia_con_f0("CGTA")
        assert res_cgta == pytest.approx(0.892341)
        
        # ATCG
        res_atcg = codificador.resonancia_con_f0("ATCG")
        assert res_atcg == pytest.approx(0.623456)
    
    def test_analizar_secuencia_completo(self):
        """Test: análisis completo de secuencia."""
        codificador = CodificadorADNRiemann()
        analisis = codificador.analizar_secuencia("GACT")
        
        # Verificar campos presentes
        assert 'secuencia' in analisis
        assert 'longitud' in analisis
        assert 'frecuencias' in analisis
        assert 'espectro_magnitud' in analisis
        assert 'hotspots' in analisis
        assert 'num_hotspots' in analisis
        assert 'resonancia_f0' in analisis
        assert 'energia_total' in analisis
        
        # Verificar valores
        assert analisis['secuencia'] == "GACT"
        assert analisis['longitud'] == 4
        assert analisis['num_hotspots'] >= 0
        assert 0 <= analisis['resonancia_f0'] <= 1
    
    def test_hotspots_alias(self):
        """Test: método hotspots es alias de identificar_hotspots."""
        codificador = CodificadorADNRiemann()
        
        hotspots1 = codificador.identificar_hotspots("GACT")
        hotspots2 = codificador.hotspots("GACT")
        
        assert hotspots1 == hotspots2
    
    def test_case_insensitive(self):
        """Test: secuencias son case-insensitive."""
        codificador = CodificadorADNRiemann()
        
        res_upper = codificador.resonancia_con_f0("GACT")
        res_lower = codificador.resonancia_con_f0("gact")
        res_mixed = codificador.resonancia_con_f0("GaCt")
        
        assert res_upper == res_lower == res_mixed


class TestIntegracionPentagonoLogos:
    """Tests de integración del Pentágono Logos completo."""
    
    def test_curva_mordell_r0(self):
        """Test: Curva de Mordell y^2=x^3-x (r=0)."""
        curva = {
            'rango_adelico': 0,
            'L_E1': 0.9186,
            'nombre': 'Curva de Mordell'
        }
        
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        # r=0 → punto de reposo
        assert resultado['rango_bio_aritmetico'] == 0
        assert resultado['nodos_constelacion'] == 0
        assert resultado['fluidez_info_ns'] == "DISIPATIVA"
    
    def test_curva_r1_superfluidez(self):
        """Test: Curva con r=1 → superfluidez."""
        curva = {
            'rango_adelico': 1,
            'L_E1': 0.0
        }
        
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        # r=1, L(E,1)=0 → superfluidez
        assert resultado['rango_bio_aritmetico'] == 1
        assert resultado['fluidez_info_ns'] == "INFINITA"
        assert resultado['psi_bsd_qcal'] == 1.0
    
    def test_cinco_milenio_unificados(self):
        """Test: 5 Problemas del Milenio unificados."""
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['milenio_unificados'] == 5
        # Los 5: BSD, Riemann, Navier-Stokes, P-NP, ADN
    
    def test_frecuencia_fundamental_consistente(self):
        """Test: frecuencia fundamental f0 = 141.7001 Hz."""
        codificador = CodificadorADNRiemann()
        assert codificador.f0 == 141.7001
        
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        assert resultado['frecuencia_fundamental'] == 141.7001


# Tests de rendimiento y robustez
class TestRobustez:
    """Tests de robustez y casos límite."""
    
    def test_secuencia_vacia(self):
        """Test: secuencia vacía."""
        codificador = CodificadorADNRiemann()
        with pytest.raises(Exception):
            # Una secuencia vacía debería fallar o manejar gracefully
            codificador.analizar_secuencia("")
    
    def test_secuencia_larga(self):
        """Test: secuencia muy larga."""
        codificador = CodificadorADNRiemann()
        secuencia_larga = "GACT" * 100  # 400 bases
        
        analisis = codificador.analizar_secuencia(secuencia_larga)
        assert analisis['longitud'] == 400
    
    def test_base_invalida(self):
        """Test: base inválida usa valor por defecto."""
        codificador = CodificadorADNRiemann()
        # 'X' no es una base válida
        frecuencias = codificador.codificar_secuencia("GXCT")
        
        # Debe tener 4 frecuencias (X → ratio por defecto 1.0)
        assert len(frecuencias) == 4
    
    def test_valores_extremos_L_E1(self):
        """Test: valores extremos de L(E,1)."""
        # L(E,1) muy grande
        curva_grande = {
            'rango_adelico': 0,
            'L_E1': 1000.0
        }
        resultado = sincronizar_bsd_adn(curva_grande, "GACT")
        assert resultado['psi_bsd_qcal'] == 0.0  # max(0, 1 - 1000) = 0
        
        # L(E,1) negativo (no debería ocurrir, pero testear)
        curva_negativa = {
            'rango_adelico': 0,
            'L_E1': -0.5
        }
        resultado = sincronizar_bsd_adn(curva_negativa, "GACT")
        assert resultado['psi_bsd_qcal'] >= 0.0  # Debe ser no-negativo


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
