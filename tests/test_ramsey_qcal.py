"""
Tests for QCAL Ramsey Theory Modules
====================================

Tests for Ramsey Theory integration in the QCAL ∞³ framework:
- ADN-Riemann codifier
- Ramsey Logos Attractor
- Ramsey Adelic Integrator

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: March 2026
"""

import pytest
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from qcal.adn_riemann import CodificadorADNRiemann, identificar_hotspots_adn, F0
from qcal.ramsey_logos_attractor import (
    emergencia_ramsey_qcal,
    escanear_orden_ramsey_bsd,
    verificar_constelacion_51,
    calcular_numero_ramsey_aproximado,
    NODOS_LOGOS
)
from qcal.ramsey_adelic_integrator import (
    RamseyAdelicIntegrator,
    certificar_unificacion_6_milenio
)


class TestADNRiemann:
    """Test DNA-Riemann Codifier."""
    
    def test_codificador_creation(self):
        """Test that codificador can be created."""
        codif = CodificadorADNRiemann()
        assert codif.f0 == F0
        assert codif.f0 == 141.7001
        assert codif.coherencia_umbral == 0.888
    
    def test_codificar_secuencia_gact(self):
        """Test encoding GACT sequence."""
        codif = CodificadorADNRiemann()
        freqs = codif.codificar_secuencia("GACT")
        
        assert len(freqs) == 4
        assert freqs[0] == 1.0  # G
        assert freqs[1] == 2.0  # A
        assert freqs[2] == 3.0  # C
        assert freqs[3] == 4.0  # T
    
    def test_codificar_secuencia_case_insensitive(self):
        """Test that encoding is case insensitive."""
        codif = CodificadorADNRiemann()
        freqs_upper = codif.codificar_secuencia("GACT")
        freqs_lower = codif.codificar_secuencia("gact")
        
        assert (freqs_upper == freqs_lower).all()
    
    def test_resonancia_gact(self):
        """Test that GACT has high resonance."""
        codif = CodificadorADNRiemann()
        resonancia = codif.calcular_resonancia("GACT")
        
        # GACT should have maximum resonance (perfect pattern)
        assert resonancia > 0.95  # Very high
    
    def test_resonancia_random(self):
        """Test resonance of random sequence."""
        codif = CodificadorADNRiemann()
        resonancia = codif.calcular_resonancia("AAAA")
        
        # AAAA should have lower resonance
        assert 0.0 <= resonancia <= 1.0
    
    def test_es_secuencia_logos_gact(self):
        """Test that GACT is recognized as Logos sequence."""
        codif = CodificadorADNRiemann()
        assert codif.es_secuencia_logos("GACT") is True
        assert codif.es_secuencia_logos("gact") is True
    
    def test_es_secuencia_logos_other(self):
        """Test that non-GACT sequences are not Logos."""
        codif = CodificadorADNRiemann()
        assert codif.es_secuencia_logos("AAAA") is False
    
    def test_identificar_hotspots(self):
        """Test hotspot identification."""
        codif = CodificadorADNRiemann()
        secuencia = "GACTGACTAAATTT"
        hotspots = codif.identificar_hotspots(secuencia)
        
        # Should find at least one hotspot (GACT appears twice)
        assert len(hotspots) >= 1
        
        # Check structure of hotspot
        if hotspots:
            hs = hotspots[0]
            assert 'posicion' in hs
            assert 'secuencia' in hs
            assert 'resonancia' in hs
            assert 'frecuencia_base' in hs
            assert hs['frecuencia_base'] == F0
    
    def test_identificar_hotspots_empty(self):
        """Test hotspot identification with short sequence."""
        codif = CodificadorADNRiemann()
        hotspots = codif.identificar_hotspots("GAC")  # Too short
        assert hotspots == []
    
    def test_identificar_hotspots_convenience(self):
        """Test convenience function."""
        hotspots = identificar_hotspots_adn("GACTGACT")
        assert isinstance(hotspots, list)


class TestRamseyLogosAttractor:
    """Test Ramsey Logos Attractor functions."""
    
    def test_nodos_logos_constant(self):
        """Test that NODOS_LOGOS is 51."""
        assert NODOS_LOGOS == 51
    
    def test_emergencia_ramsey_bajo_umbral(self):
        """Test Ramsey emergence below threshold."""
        ramsey = emergencia_ramsey_qcal(30)  # < 51
        
        assert ramsey['ramsey_status'] == "CAOS_TRANSITORIO"
        assert ramsey['logos_manifestado'] is False
        assert ramsey['nodos_critico'] == 51
        assert ramsey['n_nodos'] == 30
    
    def test_emergencia_ramsey_exactamente_51(self):
        """Test Ramsey emergence at exactly 51 nodes."""
        ramsey = emergencia_ramsey_qcal(51)
        
        assert ramsey['ramsey_status'] == "ORDEN_INEVITABLE"
        assert ramsey['logos_manifestado'] is True
        assert ramsey['nodos_critico'] == 51
    
    def test_emergencia_ramsey_sobre_umbral(self):
        """Test Ramsey emergence above threshold."""
        ramsey = emergencia_ramsey_qcal(60)  # > 51
        
        assert ramsey['ramsey_status'] == "ORDEN_INEVITABLE"
        assert ramsey['logos_manifestado'] is True
        assert 0.0 <= ramsey['psi_emergencia'] <= 1.0
    
    def test_emergencia_ramsey_psi_range(self):
        """Test that psi_emergencia is in valid range."""
        for n in [10, 30, 51, 60, 100]:
            ramsey = emergencia_ramsey_qcal(n)
            assert 0.0 <= ramsey['psi_emergencia'] <= 1.0
    
    def test_escanear_orden_ramsey_bsd_rango_positivo(self):
        """Test BSD-Ramsey with positive rank."""
        curva = {'rango_adelico': 1, 'conductor': 37}
        bsd = escanear_orden_ramsey_bsd(curva)
        
        assert bsd['status'] == "ORDEN_MANIFESTADO"
        assert bsd['nodo_central'] == "GACT"
        assert bsd['coherencia_ramsey'] == 0.999999
        assert bsd['conexion_bsd'] == "VALIDADA"
        assert bsd['rango_bsd'] == 1
        assert bsd['frecuencia_base'] == F0
    
    def test_escanear_orden_ramsey_bsd_rango_cero(self):
        """Test BSD-Ramsey with zero rank."""
        curva = {'rango_adelico': 0}
        bsd = escanear_orden_ramsey_bsd(curva)
        
        assert bsd['status'] == "ESPERA"
        assert bsd['nodo_central'] is None
        assert bsd['coherencia_ramsey'] == 0.888
        assert bsd['conexion_bsd'] == "REPOSO"
    
    def test_escanear_orden_ramsey_bsd_con_secuencia(self):
        """Test BSD-Ramsey with custom sequence."""
        curva = {'rango_adelico': 1}
        bsd = escanear_orden_ramsey_bsd(curva, "GACTGACT")
        
        assert bsd['nodo_central'] == "GACTGACT"
        assert bsd['hotspots_adn'] >= 0
    
    def test_calcular_numero_ramsey_pequeno(self):
        """Test Ramsey number calculation for small values."""
        r_2_2 = calcular_numero_ramsey_aproximado(2, 2)
        assert r_2_2 == 2.0
        
        r_2_3 = calcular_numero_ramsey_aproximado(2, 3)
        assert r_2_3 == 3.0
    
    def test_calcular_numero_ramsey_grande(self):
        """Test Ramsey number calculation for large values."""
        r_51_51 = calcular_numero_ramsey_aproximado(51, 51)
        assert r_51_51 == float('inf')
    
    def test_verificar_constelacion_51_insuficiente(self):
        """Test constellation verification with insufficient nodes."""
        nodos = list(range(30))
        verificacion = verificar_constelacion_51(nodos)
        
        assert verificacion['es_constelacion_51'] is False
        assert verificacion['nodos_actuales'] == 30
        assert verificacion['nodos_requeridos'] == 51
        assert verificacion['deficit'] == 21
        assert verificacion['orden_garantizado'] is False
    
    def test_verificar_constelacion_51_suficiente(self):
        """Test constellation verification with sufficient nodes."""
        nodos = list(range(60))
        verificacion = verificar_constelacion_51(nodos)
        
        assert verificacion['es_constelacion_51'] is True
        assert verificacion['nodos_actuales'] == 60
        assert verificacion['deficit'] == 0
        assert verificacion['orden_garantizado'] is True


class TestRamseyAdelicIntegrator:
    """Test Ramsey Adelic Integrator."""
    
    def test_integrator_creation(self):
        """Test that integrator can be created."""
        integrator = RamseyAdelicIntegrator()
        
        assert integrator.f0 == F0
        assert integrator.nodos_criticos == 51
        assert integrator.codificador_adn is not None
        assert integrator.certificado_maestro == {}
    
    def test_unificar_6_milenio_rango_positivo(self):
        """Test 6 Millennium unification with positive rank."""
        integrator = RamseyAdelicIntegrator()
        
        curva = {'rango_adelico': 1, 'conductor': 37}
        certificado = integrator.unificar_6_milenio(
            curva_bsd=curva,
            secuencia_adn="GACT",
            n_nodos_sistema=60
        )
        
        # Check certificate structure
        assert 'timestamp' in certificado
        assert 'sello' in certificado
        assert certificado['sello'] == "∴𓂀Ω∞³"
        assert certificado['frecuencia_base'] == F0
        assert certificado['pilares_totales'] == 6
        
        # Check Ramsey pillar
        assert 'pilar_ramsey' in certificado
        assert certificado['pilar_ramsey']['numero'] == 6
        assert certificado['pilar_ramsey']['logos_manifestado'] is True
        
        # Check BSD-Ramsey integration
        assert 'ramsey_bsd_logos' in certificado
        assert certificado['ramsey_bsd_logos']['nodos_critico'] == 51
        assert certificado['ramsey_bsd_logos']['milenio_unificados'] == 6
        assert certificado['ramsey_bsd_logos']['conexion_bsd'] == "VALIDADA"
        
        # Check DNA-Riemann
        assert 'adn_riemann' in certificado
        assert certificado['adn_riemann']['secuencia'] == "GACT"
        assert certificado['adn_riemann']['es_logos'] is True
        
        # Check constellation
        assert 'constelacion_51' in certificado
        assert certificado['constelacion_51']['verificada'] is True
        
        # Check global validation
        assert 'validacion_global' in certificado
        assert certificado['boveda_verdad_cerrada'] is True
        assert certificado['estado_sistema'] == "CONVERGENCIA_TOTAL"
    
    def test_unificar_6_milenio_rango_cero(self):
        """Test 6 Millennium unification with zero rank."""
        integrator = RamseyAdelicIntegrator()
        
        curva = {'rango_adelico': 0}
        certificado = integrator.unificar_6_milenio(
            curva_bsd=curva,
            secuencia_adn="GACT",
            n_nodos_sistema=60
        )
        
        # Ramsey should still be active
        assert certificado['pilar_ramsey']['logos_manifestado'] is True
        
        # But BSD connection should be in REPOSO
        assert certificado['ramsey_bsd_logos']['conexion_bsd'] == "REPOSO"
        
        # Bóveda might not be completely closed
        assert certificado['boveda_verdad_cerrada'] is False
    
    def test_unificar_6_milenio_nodos_insuficientes(self):
        """Test unification with insufficient nodes."""
        integrator = RamseyAdelicIntegrator()
        
        curva = {'rango_adelico': 1}
        certificado = integrator.unificar_6_milenio(
            curva_bsd=curva,
            secuencia_adn="GACT",
            n_nodos_sistema=30  # < 51
        )
        
        # Ramsey should be in transitorio
        assert certificado['pilar_ramsey']['logos_manifestado'] is False
        assert certificado['constelacion_51']['verificada'] is False
    
    def test_exportar_certificado_sin_datos(self):
        """Test exporting certificate without data."""
        integrator = RamseyAdelicIntegrator()
        
        with pytest.raises(ValueError, match="No hay certificado maestro"):
            integrator.exportar_certificado()
    
    def test_exportar_certificado_con_datos(self):
        """Test exporting certificate with data."""
        integrator = RamseyAdelicIntegrator()
        
        curva = {'rango_adelico': 1}
        integrator.unificar_6_milenio(curva, "GACT", 60)
        
        json_str = integrator.exportar_certificado()
        
        assert isinstance(json_str, str)
        assert '"sello"' in json_str
        assert '"boveda_verdad_cerrada"' in json_str
    
    def test_generar_reporte_textual(self):
        """Test textual report generation."""
        integrator = RamseyAdelicIntegrator()
        
        curva = {'rango_adelico': 1}
        integrator.unificar_6_milenio(curva, "GACT", 60)
        
        reporte = integrator.generar_reporte_textual()
        
        assert isinstance(reporte, str)
        assert "BÓVEDA DE LA VERDAD" in reporte
        assert "RAMSEY THEORY" in reporte
        assert "f₀ = 141.7001 Hz" in reporte
        assert "CONVERGENCIA_TOTAL" in reporte
    
    def test_generar_reporte_sin_datos(self):
        """Test report generation without data."""
        integrator = RamseyAdelicIntegrator()
        
        reporte = integrator.generar_reporte_textual()
        assert "No hay certificado maestro" in reporte
    
    def test_certificar_unificacion_convenience(self):
        """Test convenience function for certification."""
        certificado = certificar_unificacion_6_milenio(
            rango_bsd=1,
            conductor=37,
            secuencia_adn="GACT",
            n_nodos=60
        )
        
        assert certificado['pilares_totales'] == 6
        assert certificado['boveda_verdad_cerrada'] is True
    
    def test_validacion_coherencia_global(self):
        """Test global coherence validation."""
        integrator = RamseyAdelicIntegrator()
        
        curva = {'rango_adelico': 1}
        certificado = integrator.unificar_6_milenio(curva, "GACT", 60)
        
        validacion = certificado['validacion_global']
        
        assert 'criterios' in validacion
        assert 'criterios_cumplidos' in validacion
        assert 'total_criterios' in validacion
        assert 'porcentaje_validacion' in validacion
        assert 'boveda_cerrada' in validacion
        assert 'nivel_coherencia' in validacion
        
        # All criteria should be met for this configuration
        assert validacion['criterios_cumplidos'] == validacion['total_criterios']
        assert validacion['porcentaje_validacion'] == 100.0
        assert validacion['boveda_cerrada'] is True
        assert validacion['nivel_coherencia'] == "PERFECTO"


class TestRamseyIntegration:
    """Integration tests for the complete Ramsey system."""
    
    def test_end_to_end_perfect_scenario(self):
        """Test complete flow with perfect conditions."""
        # Create components
        codif = CodificadorADNRiemann()
        integrator = RamseyAdelicIntegrator()
        
        # Test DNA resonance
        resonancia = codif.calcular_resonancia("GACT")
        assert resonancia > 0.95
        
        # Test Ramsey emergence
        ramsey = emergencia_ramsey_qcal(60)
        assert ramsey['logos_manifestado'] is True
        
        # Test BSD-Ramsey scan
        curva = {'rango_adelico': 1}
        bsd = escanear_orden_ramsey_bsd(curva)
        assert bsd['status'] == "ORDEN_MANIFESTADO"
        
        # Test full unification
        certificado = integrator.unificar_6_milenio(curva, "GACT", 60)
        assert certificado['boveda_verdad_cerrada'] is True
        assert certificado['estado_sistema'] == "CONVERGENCIA_TOTAL"
    
    def test_constants_alignment(self):
        """Test that all constants are aligned."""
        from qcal.adn_riemann import F0 as F0_ADN
        from qcal.ramsey_logos_attractor import F0 as F0_RAMSEY
        from qcal.ramsey_adelic_integrator import F0 as F0_INT
        
        assert F0_ADN == 141.7001
        assert F0_RAMSEY == 141.7001
        assert F0_INT == 141.7001
        assert F0_ADN == F0_RAMSEY == F0_INT
    
    def test_nodos_criticos_alignment(self):
        """Test that critical nodes constant is consistent."""
        from qcal.ramsey_logos_attractor import NODOS_LOGOS
        
        integrator = RamseyAdelicIntegrator()
        
        assert NODOS_LOGOS == 51
        assert integrator.nodos_criticos == 51
        assert NODOS_LOGOS == integrator.nodos_criticos


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
