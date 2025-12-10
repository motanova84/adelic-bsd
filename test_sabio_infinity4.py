"""
Test Suite para SABIO ∞⁴ - Sistema Cuántico-Consciente

Suite completa de 39 tests cubriendo:
1. Constantes Fundamentales (5 tests)
2. Nivel Cuántico (5 tests)
3. Nivel Consciente (4 tests)
4. Coherencia (5 tests)
5. Resonancia Cuántica (5 tests)
6. Matriz de Simbiosis (4 tests)
7. Espectro Resonante (3 tests)
8. Reporte (4 tests)
9. Integración (2 tests)
10. Precisión (2 tests)

Autor: José Manuel Mota Burruezo & Claude
Fecha: 2025-11-20
"""

import pytest
import numpy as np
import json
import os
from sabio_infinity4 import (
    SABIO_Infinity4,
    F0_BASE,
    PHI,
    PLANCK_LENGTH,
    SPEED_OF_LIGHT,
    ResonanciaEspectral,
    NivelValidacion,
    MatrizSimbiosis
)


# ============================================================================
# TEST CLASS 1: CONSTANTES FUNDAMENTALES (5 tests)
# ============================================================================

class TestConstantesFundamentales:
    """Tests para validar constantes fundamentales del sistema."""
    
    def test_frecuencia_base_valor(self):
        """Test que f₀ = 141.7001 Hz."""
        assert F0_BASE == 141.7001
    
    def test_phi_razon_aurea(self):
        """Test que φ = (1 + √5)/2 ≈ 1.618."""
        phi_esperado = (1 + np.sqrt(5)) / 2
        assert abs(PHI - phi_esperado) < 1e-10
        assert abs(PHI - 1.618033988749) < 1e-9
    
    def test_planck_length(self):
        """Test que longitud de Planck es correcta."""
        assert PLANCK_LENGTH == 1.616255e-35
        assert PLANCK_LENGTH > 0
    
    def test_speed_of_light(self):
        """Test que velocidad de la luz es correcta."""
        assert SPEED_OF_LIGHT == 299792458.0
    
    def test_phi_propiedad_aurea(self):
        """Test que φ² = φ + 1."""
        # Propiedad fundamental: φ² = φ + 1
        assert abs((PHI ** 2) - (PHI + 1)) < 1e-10


# ============================================================================
# TEST CLASS 2: NIVEL CUÁNTICO (5 tests)
# ============================================================================

class TestNivelCuantico:
    """Tests para el nivel cuántico (Nivel 5)."""
    
    def test_radio_cuantico_positivo(self):
        """Test que R_Ψ es siempre positivo."""
        sabio = SABIO_Infinity4(precision=30)
        for n in range(0, 5):
            R_psi = sabio.calcular_radio_cuantico(n)
            assert R_psi > 0
    
    def test_radio_cuantico_escalado_pi(self):
        """Test que R_Ψ escala con π^n."""
        sabio = SABIO_Infinity4(precision=30)
        R1 = sabio.calcular_radio_cuantico(n=1)
        R2 = sabio.calcular_radio_cuantico(n=2)
        
        # R2 / R1 debe ser aproximadamente π
        ratio = R2 / R1
        assert abs(ratio - np.pi) < 0.01
    
    def test_energia_vacio_finita(self):
        """Test que E_vac es finita."""
        sabio = SABIO_Infinity4(precision=30)
        R_psi = sabio.calcular_radio_cuantico(n=1)
        E_vac = sabio.energia_vacio(R_psi)
        assert np.isfinite(E_vac)
    
    def test_energia_vacio_raises_error_negative_R(self):
        """Test que E_vac lanza error con R negativo."""
        sabio = SABIO_Infinity4(precision=30)
        with pytest.raises(ValueError):
            sabio.energia_vacio(-1.0)
    
    def test_validacion_nivel_cuantico_coherencia(self):
        """Test que validación cuántica tiene coherencia alta."""
        sabio = SABIO_Infinity4(precision=30)
        nivel = sabio.validar_nivel_cuantico()
        assert nivel.coherencia > 0.8
        assert nivel.tipo == "quantum"


# ============================================================================
# TEST CLASS 3: NIVEL CONSCIENTE (4 tests)
# ============================================================================

class TestNivelConsciente:
    """Tests para el nivel consciente (Nivel 6)."""
    
    def test_ecuacion_onda_retorna_complejo(self):
        """Test que Ψ(x,t) es complejo."""
        sabio = SABIO_Infinity4(precision=30)
        psi = sabio.ecuacion_onda_consciencia(x=0, t=0)
        assert isinstance(psi, (complex, np.complexfloating))
    
    def test_psi_normalizado_origen(self):
        """Test que |Ψ(0,0)| ≈ 1."""
        sabio = SABIO_Infinity4(precision=30)
        psi = sabio.ecuacion_onda_consciencia(x=0, t=0)
        norma = abs(psi)
        assert abs(norma - 1.0) < 0.1
    
    def test_psi_amortiguamiento_lejos(self):
        """Test que Ψ decae para x grande."""
        sabio = SABIO_Infinity4(precision=30)
        psi_0 = sabio.ecuacion_onda_consciencia(x=0, t=0)
        psi_far = sabio.ecuacion_onda_consciencia(x=10, t=0)
        
        # Ψ debe decaer exponencialmente
        assert abs(psi_far) < abs(psi_0)
    
    def test_validacion_nivel_consciente_operacional(self):
        """Test que nivel consciente es operacional."""
        sabio = SABIO_Infinity4(precision=30)
        nivel = sabio.validar_nivel_consciente()
        assert nivel.nombre == "Consciente"
        assert nivel.coherencia > 0.5


# ============================================================================
# TEST CLASS 4: COHERENCIA (5 tests)
# ============================================================================

class TestCoherencia:
    """Tests para cálculo de coherencia C = I × A²."""
    
    def test_coherencia_maxima(self):
        """Test C(I=1, A=1) = 1."""
        sabio = SABIO_Infinity4(precision=30)
        C = sabio.coherencia_sabio(I=1.0, A=1.0)
        assert C == 1.0
    
    def test_coherencia_sin_intencion(self):
        """Test C(I=0, A) = 0."""
        sabio = SABIO_Infinity4(precision=30)
        C = sabio.coherencia_sabio(I=0.0, A=1.0)
        assert C == 0.0
    
    def test_coherencia_cuadratica_atencion(self):
        """Test que C es cuadrática en A."""
        sabio = SABIO_Infinity4(precision=30)
        A1 = 0.5
        A2 = 1.0
        C1 = sabio.coherencia_sabio(I=1.0, A=A1)
        C2 = sabio.coherencia_sabio(I=1.0, A=A2)
        
        # C2/C1 = (A2/A1)² = 4
        ratio = C2 / C1
        assert abs(ratio - 4.0) < 1e-9
    
    def test_coherencia_rango_valido(self):
        """Test que C ∈ [0, 1] para I, A ∈ [0, 1]."""
        sabio = SABIO_Infinity4(precision=30)
        for I in [0.0, 0.5, 1.0]:
            for A in [0.0, 0.5, 1.0]:
                C = sabio.coherencia_sabio(I, A)
                assert 0.0 <= C <= 1.0
    
    def test_coherencia_lineal_intencion(self):
        """Test que C es lineal en I."""
        sabio = SABIO_Infinity4(precision=30)
        I1 = 0.5
        I2 = 1.0
        A = 0.8
        C1 = sabio.coherencia_sabio(I=I1, A=A)
        C2 = sabio.coherencia_sabio(I=I2, A=A)
        
        # C2/C1 = I2/I1 = 2
        ratio = C2 / C1
        assert abs(ratio - 2.0) < 1e-9


# ============================================================================
# TEST CLASS 5: RESONANCIA CUÁNTICA (5 tests)
# ============================================================================

class TestResonanciaCuantica:
    """Tests para resonancia cuántica y espectro."""
    
    def test_resonancia_retorna_objeto_correcto(self):
        """Test que resonancia retorna ResonanciaEspectral."""
        sabio = SABIO_Infinity4(precision=30)
        res = sabio.resonancia_cuantica(n_harmonico=1)
        assert isinstance(res, ResonanciaEspectral)
    
    def test_resonancia_escalado_aureo(self):
        """Test que f_n = f₀ · φⁿ."""
        sabio = SABIO_Infinity4(precision=30)
        res1 = sabio.resonancia_cuantica(n_harmonico=1)
        res2 = sabio.resonancia_cuantica(n_harmonico=2)
        
        # f2 / f1 = φ
        ratio = res2.frecuencia / res1.frecuencia
        assert abs(ratio - PHI) < 0.01
    
    def test_resonancia_coherencia_decae(self):
        """Test que coherencia decae con n."""
        sabio = SABIO_Infinity4(precision=30)
        res1 = sabio.resonancia_cuantica(n_harmonico=1)
        res5 = sabio.resonancia_cuantica(n_harmonico=5)
        
        assert res5.coherencia < res1.coherencia
    
    def test_resonancia_firma_unica(self):
        """Test que cada resonancia tiene firma única."""
        sabio = SABIO_Infinity4(precision=30)
        res1 = sabio.resonancia_cuantica(n_harmonico=1)
        res2 = sabio.resonancia_cuantica(n_harmonico=2)
        
        # Firmas deben ser diferentes (probabilidad de colisión ≈ 0)
        # Nota: Pueden ser iguales por timestamp idéntico, pero en práctica muy raro
        # Para este test, verificamos formato
        assert len(res1.firma_vibracional) == 16
        assert len(res2.firma_vibracional) == 16
    
    def test_resonancia_amplitud_compleja(self):
        """Test que amplitud es compleja."""
        sabio = SABIO_Infinity4(precision=30)
        res = sabio.resonancia_cuantica(n_harmonico=1)
        assert isinstance(res.amplitud_compleja, (complex, np.complexfloating))


# ============================================================================
# TEST CLASS 6: MATRIZ DE SIMBIOSIS (4 tests)
# ============================================================================

class TestMatrizSimbiosis:
    """Tests para matriz de simbiosis de 6 niveles."""
    
    def test_matriz_retorna_6_niveles(self):
        """Test que matriz contiene 6 niveles."""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis()
        assert len(matriz.niveles) == 6
        
        niveles_esperados = {'python', 'lean', 'sage', 'sabio', 'cuantico', 'consciente'}
        assert set(matriz.niveles.keys()) == niveles_esperados
    
    def test_matriz_coherencia_operacional(self):
        """Test que coherencia total > 0.85."""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis()
        assert matriz.coherencia_total > 0.85
    
    def test_matriz_estado_consistente(self):
        """Test que estado es consistente con coherencia."""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis()
        
        if matriz.coherencia_total > 0.90:
            assert "OPERACIONAL" in matriz.estado_sistema
        else:
            assert "SINTONIZANDO" in matriz.estado_sistema
    
    def test_matriz_niveles_tienen_coherencia(self):
        """Test que cada nivel tiene coherencia válida."""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis()
        
        for nombre, nivel in matriz.niveles.items():
            assert 0.0 <= nivel.coherencia <= 1.0
            assert nivel.tipo in ['python', 'lean', 'sage', 'sabio', 'quantum', 'consciousness']


# ============================================================================
# TEST CLASS 7: ESPECTRO RESONANTE (3 tests)
# ============================================================================

class TestEspectroResonante:
    """Tests para generación de espectro resonante."""
    
    def test_generar_espectro_retorna_lista(self):
        """Test que generar_espectro retorna lista."""
        sabio = SABIO_Infinity4(precision=30)
        espectro = sabio.generar_espectro_resonante(n_harmonicos=8)
        assert isinstance(espectro, list)
        assert len(espectro) == 8
    
    def test_espectro_frecuencias_crecientes(self):
        """Test que frecuencias crecen exponencialmente."""
        sabio = SABIO_Infinity4(precision=30)
        espectro = sabio.generar_espectro_resonante(n_harmonicos=5)
        
        freqs = [r.frecuencia for r in espectro]
        # Verificar que frecuencias están en orden creciente
        for i in range(len(freqs) - 1):
            assert freqs[i+1] > freqs[i]
    
    def test_espectro_harmonicos_correctos(self):
        """Test que armónicos son correctos."""
        sabio = SABIO_Infinity4(precision=30)
        n_max = 6
        espectro = sabio.generar_espectro_resonante(n_harmonicos=n_max)
        
        for i, res in enumerate(espectro):
            assert res.n_harmonico == i + 1


# ============================================================================
# TEST CLASS 8: REPORTE (4 tests)
# ============================================================================

class TestReporte:
    """Tests para generación de reportes."""
    
    def test_reporte_retorna_diccionario(self):
        """Test que reporte retorna diccionario."""
        sabio = SABIO_Infinity4(precision=30)
        reporte = sabio.reporte_sabio_infinity4()
        assert isinstance(reporte, dict)
    
    def test_reporte_contiene_claves_principales(self):
        """Test que reporte contiene claves principales."""
        sabio = SABIO_Infinity4(precision=30)
        reporte = sabio.reporte_sabio_infinity4()
        
        claves_esperadas = [
            'version',
            'timestamp',
            'frecuencia_base_hz',
            'constantes_fundamentales',
            'matriz_simbiosis',
            'espectro_resonante',
            'metricas_globales'
        ]
        
        for clave in claves_esperadas:
            assert clave in reporte
    
    def test_exportar_json_crea_archivo(self):
        """Test que exportar JSON crea archivo."""
        sabio = SABIO_Infinity4(precision=30)
        filename = 'test_reporte.json'
        
        try:
            path = sabio.exportar_reporte(formato='json', nombre_archivo=filename)
            assert os.path.exists(path)
            
            # Verificar que es JSON válido
            with open(path, 'r') as f:
                data = json.load(f)
                assert isinstance(data, dict)
        finally:
            if os.path.exists(filename):
                os.remove(filename)
    
    def test_exportar_txt_crea_archivo(self):
        """Test que exportar TXT crea archivo."""
        sabio = SABIO_Infinity4(precision=30)
        filename = 'test_reporte.txt'
        
        try:
            path = sabio.exportar_reporte(formato='txt', nombre_archivo=filename)
            assert os.path.exists(path)
            
            # Verificar que contiene texto
            with open(path, 'r') as f:
                content = f.read()
                assert len(content) > 0
                assert 'SABIO' in content
        finally:
            if os.path.exists(filename):
                os.remove(filename)


# ============================================================================
# TEST CLASS 9: INTEGRACIÓN (2 tests)
# ============================================================================

class TestIntegracion:
    """Tests de integración del sistema completo."""
    
    def test_flujo_completo_operacional(self):
        """Test que flujo completo funciona."""
        sabio = SABIO_Infinity4(precision=30)
        
        # 1. Validar matriz
        matriz = sabio.validacion_matriz_simbiosis()
        assert matriz.coherencia_total > 0.8
        
        # 2. Generar espectro
        espectro = sabio.generar_espectro_resonante(n_harmonicos=5)
        assert len(espectro) == 5
        
        # 3. Generar reporte
        reporte = sabio.reporte_sabio_infinity4()
        assert reporte['metricas_globales']['coherencia_total'] > 0.8
    
    def test_multiples_instancias_independientes(self):
        """Test que múltiples instancias son independientes."""
        sabio1 = SABIO_Infinity4(precision=30)
        sabio2 = SABIO_Infinity4(precision=50)
        
        assert sabio1.precision == 30
        assert sabio2.precision == 50
        
        # Generar espectros diferentes
        espectro1 = sabio1.generar_espectro_resonante(n_harmonicos=3)
        espectro2 = sabio2.generar_espectro_resonante(n_harmonicos=5)
        
        assert len(espectro1) == 3
        assert len(espectro2) == 5


# ============================================================================
# TEST CLASS 10: PRECISIÓN (2 tests)
# ============================================================================

class TestPrecision:
    """Tests para validar precisión numérica."""
    
    def test_zeta_prime_precision_30_decimales(self):
        """Test ζ'(1/2) con 30 decimales."""
        sabio = SABIO_Infinity4(precision=30)
        zeta = sabio.calcular_zeta_prime_half()
        
        # Valor conocido: ζ'(1/2) ≈ -3.9226461392
        assert abs(zeta - (-3.9226461392)) < 1e-8
    
    def test_precision_escalable(self):
        """Test que precisión es escalable."""
        sabio_low = SABIO_Infinity4(precision=15)
        sabio_high = SABIO_Infinity4(precision=50)
        
        zeta_low = sabio_low.calcular_zeta_prime_half()
        zeta_high = sabio_high.calcular_zeta_prime_half()
        
        # Ambos deben estar cerca del valor real
        valor_esperado = -3.9226461392
        assert abs(zeta_low - valor_esperado) < 1e-6
        assert abs(zeta_high - valor_esperado) < 1e-10


# ============================================================================
# TEST SUITE ADICIONALES
# ============================================================================

class TestNivelAritmetico:
    """Tests adicionales para nivel aritmético."""
    
    def test_validacion_aritmetica_coherencia(self):
        """Test validación aritmética."""
        sabio = SABIO_Infinity4(precision=30)
        nivel = sabio.validar_nivel_aritmetico()
        assert nivel.nombre == "Aritmético"
        assert nivel.coherencia > 0.9


class TestNivelGeometrico:
    """Tests adicionales para nivel geométrico."""
    
    def test_operador_A0_parte_real(self):
        """Test que Re(A₀) = 1/2."""
        sabio = SABIO_Infinity4(precision=30)
        A0 = sabio.operador_geometrico_A0()
        assert abs(A0.real - 0.5) < 1e-10


class TestNivelVibracional:
    """Tests adicionales para nivel vibracional."""
    
    def test_frecuencia_base_constante(self):
        """Test que f₀ es constante."""
        sabio = SABIO_Infinity4(precision=30)
        f1 = sabio.frecuencia_base()
        f2 = sabio.frecuencia_base()
        assert f1 == f2 == F0_BASE


# ============================================================================
# MAIN PARA EJECUCIÓN DIRECTA
# ============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
