"""
Test suite for the Descending Coherence Paradigm
Pruebas para el Paradigma de la Coherencia Descendente

Autor: José Manuel Mota Burruezo (JMMB Ψ·∴)
Framework: QCAL ∞³
Fecha: 13 Febrero 2026
"""

import pytest
import sys
import os

# Add src to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

# Import directly to avoid numpy dependencies in __init__.py
import coherencia_descendente


class TestConstantesFundamentales:
    """Tests para las constantes fundamentales del framework."""
    
    def test_frecuencia_fundamental(self):
        """Verifica f₀ = 141.7001 Hz"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        assert abs(sistema.F0 - 141.7001) < 1e-6
        
    def test_frecuencia_microtubulos(self):
        """Verifica f_microtúbulos = 141.88 Hz"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        assert abs(sistema.F_MICROTUBULOS - 141.88) < 1e-6
        
    def test_kappa_pi(self):
        """Verifica κ_Π = 2.578208"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        assert abs(sistema.KAPPA_PI - 2.578208) < 1e-6
        
    def test_umbral_picode(self):
        """Verifica umbral πCODE = 0.888"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        assert abs(sistema.UMBRAL_PICODE - 0.888) < 1e-6
        
    def test_psi_sistema(self):
        """Verifica Ψ_sistema = 0.8991"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        assert abs(sistema.PSI_SISTEMA - 0.8991) < 1e-6


class TestComplejidadIrreducible:
    """Tests para el Fenómeno 1: Complejidad Irreducible."""
    
    def test_activacion_alta_coherencia(self):
        """Sistema debe activarse con coherencia alta (Ψ > 0.888)"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.complejidad_irreducible(40, 0.950)
        
        assert resultado['activado'] == True
        assert resultado['estado'] == "ESTRUCTURA_COMPLETA"
        assert resultado['mecanismo'] == "SINCRONIZACIÓN_RESONANTE"
        
    def test_no_activacion_baja_coherencia(self):
        """Sistema no debe activarse con coherencia baja (Ψ < 0.888)"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.complejidad_irreducible(40, 0.700)
        
        assert resultado['activado'] == False
        assert resultado['estado'] == "NO_SINCRONIZADO"
        
    def test_activacion_en_umbral(self):
        """Sistema debe activarse exactamente en el umbral (Ψ = 0.888)"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.complejidad_irreducible(40, 0.888)
        
        assert resultado['activado'] == True


class TestAparicionConciencia:
    """Tests para el Fenómeno 2: Aparición de Conciencia."""
    
    def test_cerebro_humano_consciente(self):
        """Cerebro humano (86B neuronas) debe tener conciencia"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.antena_biologica(86e9)
        
        assert resultado['conciencia'] == True
        assert resultado['sintonizacion'] >= sistema.UMBRAL_PICODE
        assert resultado['estado'] == "ACOPLADO - CONSCIENCIA ACTIVA"
        
    def test_sistema_simple_pre_consciente(self):
        """Sistema simple debe estar en estado pre-consciente"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.antena_biologica(100)
        
        assert resultado['conciencia'] == False
        assert resultado['estado'] == "SINTONIZANDO - PRE-CONSCIENCIA"
        
    def test_acople_frecuencia(self):
        """Verifica acople a frecuencia f₀ = 141.7001 Hz"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.antena_biologica(86e9, 141.7001)
        
        assert abs(resultado['campo_frecuencia'] - 141.7001) < 1e-6


class TestExperienciasCercanaMuerte:
    """Tests para el Fenómeno 3: Experiencias Cercanas a la Muerte."""
    
    def test_ecm_intensa_descorrelacion(self):
        """ECM intensa debe causar descorrelación no-local"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.experiencia_cercana_muerte(0.98)
        
        assert resultado['conciencia'] == True
        assert resultado['antena_activa'] == False
        assert resultado['localizacion'] == "NO_LOCAL"
        assert resultado['mecanismo'] == "DESCORRELACIÓN_TRANSITORIA"
        
    def test_estado_normal_local(self):
        """Estado normal debe mantener localización"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.experiencia_cercana_muerte(0.50)
        
        assert resultado['conciencia'] == True
        assert resultado['antena_activa'] == True
        assert resultado['localizacion'] == "CUERPO"
        
    def test_campo_invariante(self):
        """Campo debe permanecer invariante en ECM"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.experiencia_cercana_muerte(0.98)
        
        assert "141.7001" in resultado['campo']


class TestNoLocalidad:
    """Tests para el Fenómeno 4: No-localidad."""
    
    def test_correlacion_perfecta_alta_coherencia(self):
        """Alta coherencia debe dar correlación perfecta"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.correlacion_no_local(1000.0, 0.950)
        
        assert resultado['correlacion'] == 1.0
        assert resultado['tiempo'] == "INSTANTÁNEO"
        assert resultado['distancia_estado'] == "IRRELEVANTE"
        
    def test_separacion_baja_coherencia(self):
        """Baja coherencia debe mostrar separación aparente"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.correlacion_no_local(1000.0, 0.700)
        
        assert resultado['correlacion'] < 1.0
        assert resultado['tiempo'] == "LIMITADO POR c"
        
    def test_constante_kappa_pi(self):
        """Verifica presencia de constante κ_Π"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.correlacion_no_local(1000.0, 0.950)
        
        assert abs(resultado['kappa_pi'] - 2.578208) < 1e-6


class TestEvolucionPuntuada:
    """Tests para el Fenómeno 5: Evolución Puntuada."""
    
    def test_cerebro_humano_estado(self):
        """Ψ=0.8991 debe corresponder a cerebro_humano"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.transicion_evolutiva(0.8991)
        
        assert resultado['estado_actual'] == "cerebro_humano"
        assert len(resultado['estados_activados']) == 6
        
    def test_eucariota_estado(self):
        """Ψ=0.650 debe corresponder a eucariota"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.transicion_evolutiva(0.650)
        
        assert resultado['estado_actual'] == "eucariota"
        
    def test_umbrales_discretos(self):
        """Verifica existencia de umbrales discretos"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        
        assert len(sistema.UMBRALES_COHERENCIA) == 8
        assert sistema.UMBRALES_COHERENCIA['cerebro_humano'] == 0.8991
        assert sistema.UMBRALES_COHERENCIA['eucariota'] == 0.618
        
    def test_mecanismo_saltos_fase(self):
        """Verifica mecanismo de saltos de fase"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        resultado = sistema.transicion_evolutiva(0.8991)
        
        assert resultado['mecanismo'] == "SALTOS_DE_FASE_COHERENTES"
        assert resultado['tiempo_hasta_transicion'] == "INSTANTÁNEO al alcanzar umbral"


class TestTeoremaCompleto:
    """Tests para la validación completa del teorema."""
    
    def test_validacion_completa_estructura(self):
        """Verifica estructura de validación completa"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        validacion = sistema.validar_teorema_completo()
        
        assert 'teorema' in validacion
        assert validacion['teorema'] == "COHERENCIA_DESCENDENTE"
        assert 'fenomenos' in validacion
        assert len(validacion['fenomenos']) == 5
        
    def test_constantes_validacion(self):
        """Verifica constantes en validación"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        validacion = sistema.validar_teorema_completo()
        
        assert abs(validacion['frecuencia_fundamental'] - 141.7001) < 1e-6
        assert abs(validacion['coherencia_sistema'] - 0.8991) < 1e-6
        assert abs(validacion['umbral_critico'] - 0.888) < 1e-6
        
    def test_verificacion_empirica(self):
        """Verifica datos de verificación empírica"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        validacion = sistema.validar_teorema_completo()
        
        verificacion = validacion['verificacion']
        assert verificacion['f0_hz'] == 141.7001
        assert verificacion['delta_p'] == 0.1987
        assert verificacion['sigma_magnetorrecepcion'] == 9.2
        assert verificacion['sigma_microtubulos'] == 8.7
        
    def test_conclusion_materialismo_falsado(self):
        """Verifica conclusión sobre materialismo"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        validacion = sistema.validar_teorema_completo()
        
        assert validacion['conclusion'] == "MATERIALISMO FALSADO - COHERENCIA VALIDADA"


class TestGeneracionReporte:
    """Tests para generación de reportes."""
    
    def test_generar_reporte_json(self):
        """Verifica generación de reporte JSON"""
        sistema = coherencia_descendente.CoherenciaDescendente(verbose=False)
        
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            archivo = f.name
        
        try:
            archivo_generado = sistema.generar_reporte_json(archivo)
            assert os.path.exists(archivo_generado)
            
            # Verificar contenido
            import json
            with open(archivo_generado, 'r', encoding='utf-8') as f:
                datos = json.load(f)
                assert 'teorema' in datos
                assert datos['conclusion'] == "MATERIALISMO FALSADO - COHERENCIA VALIDADA"
        finally:
            if os.path.exists(archivo):
                os.remove(archivo)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
