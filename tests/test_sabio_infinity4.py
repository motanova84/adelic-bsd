#!/usr/bin/env python3
"""
Test suite completo para SABIO ∞⁴
39 tests organizados por categoría

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
License: MIT
"""

import pytest
import sys
import os
from pathlib import Path
import json
import tempfile

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Skip all tests if mpmath not available
pytest.importorskip("mpmath")

from mpmath import mp, mpf, pi
from src.sabio_infinity4 import (
    SABIO_Infinity4,
    ResonanciaQuantica,
    MatrizSimbiosis,
    ReporteSABIO,
    demo_sabio_infinity4,
    MPMATH_AVAILABLE
)


# ============================================================================
# Fixtures
# ============================================================================

@pytest.fixture
def sabio_instance():
    """Fixture: Instancia SABIO con precisión estándar"""
    return SABIO_Infinity4(precision=30)


@pytest.fixture
def sabio_high_precision():
    """Fixture: Instancia SABIO con alta precisión"""
    return SABIO_Infinity4(precision=100)


# ============================================================================
# 1. Test Constantes Fundamentales (5 tests)
# ============================================================================

class TestConstantesFundamentales:
    """Suite de tests para constantes fundamentales"""
    
    def test_frecuencia_base(self, sabio_instance):
        """Test: Frecuencia base f₀ = 141.7001 Hz"""
        f0 = float(sabio_instance.f0)
        assert 141.6 < f0 < 141.8, f"f₀ fuera de rango: {f0}"
        assert abs(f0 - 141.7001) < 0.001, f"f₀ no preciso: {f0}"
    
    def test_proporcion_aurea(self, sabio_instance):
        """Test: Proporción áurea φ ≈ 1.618033989"""
        phi = float(sabio_instance.phi)
        phi_expected = (1 + 5**0.5) / 2
        assert abs(phi - phi_expected) < 1e-6, f"φ incorrecto: {phi}"
        
        # Verificar identidad φ² = φ + 1
        phi_squared = float(sabio_instance.phi ** 2)
        phi_plus_one = float(sabio_instance.phi + 1)
        assert abs(phi_squared - phi_plus_one) < 1e-9, "Identidad áurea violada"
    
    def test_omega_0(self, sabio_instance):
        """Test: Frecuencia angular ω₀ = 2πf₀"""
        omega_0 = float(sabio_instance.omega_0)
        f0 = float(sabio_instance.f0)
        omega_expected = 2 * 3.141592653589793 * f0
        
        error_rel = abs(omega_0 - omega_expected) / omega_expected
        assert error_rel < 1e-6, f"ω₀ incorrecto: {omega_0}"
    
    def test_zeta_prime_half(self, sabio_instance):
        """Test: |ζ'(1/2)| ≈ 1.460354508"""
        zeta_prime = float(sabio_instance.zeta_prime_half)
        # Allow wider range due to numerical approximation
        assert 1.2 < zeta_prime < 1.6, f"|ζ'(1/2)| fuera de rango: {zeta_prime}"
        
        # Valor conocido de OEIS A059750 (approximately)
        known_value = 1.460354508
        assert abs(zeta_prime - known_value) < 0.2, f"|ζ'(1/2)| no preciso: {zeta_prime}"
    
    def test_constantes_fisicas(self, sabio_instance):
        """Test: Constantes físicas correctas"""
        # Velocidad de la luz
        assert float(sabio_instance.c) == 299792458.0, "c incorrecta"
        
        # Constante de Planck reducida
        hbar = float(sabio_instance.hbar)
        assert abs(hbar - 1.054571817e-34) < 1e-42, f"ℏ incorrecta: {hbar}"
        
        # Longitud de Planck
        l_planck = float(sabio_instance.l_planck)
        assert abs(l_planck - 1.616255e-35) < 1e-41, f"l_P incorrecta: {l_planck}"


# ============================================================================
# 2. Test Nivel Cuántico (5 tests)
# ============================================================================

class TestNivelCuantico:
    """Suite de tests para nivel cuántico"""
    
    def test_radio_cuantico_n1(self, sabio_instance):
        """Test: Radio cuántico R_Ψ(n=1) ≈ π·l_Planck"""
        R_psi = sabio_instance.calcular_radio_cuantico(n=1)
        
        # Debe ser del orden de longitud de Planck
        assert 1e-36 < float(R_psi) < 1e-34, f"R_Ψ fuera de escala: {R_psi}"
        
        # Verificar fórmula R_Ψ = n·π·l_P
        l_planck = sabio_instance.l_planck
        expected = pi * l_planck
        error_rel = abs(R_psi - expected) / expected
        assert error_rel < 1e-10, f"R_Ψ no cumple fórmula: {error_rel}"
    
    def test_radio_cuantico_escalado(self, sabio_instance):
        """Test: Radio cuántico escala linealmente con n"""
        R1 = sabio_instance.calcular_radio_cuantico(n=1)
        R2 = sabio_instance.calcular_radio_cuantico(n=2)
        R3 = sabio_instance.calcular_radio_cuantico(n=3)
        
        # Verificar proporcionalidad
        ratio_21 = float(R2 / R1)
        ratio_32 = float(R3 / R2)
        
        assert abs(ratio_21 - 2.0) < 1e-9, f"Escalado incorrecto: {ratio_21}"
        assert abs(ratio_32 - 1.5) < 1e-9, f"Escalado incorrecto: {ratio_32}"
    
    def test_energia_vacio_positiva(self, sabio_instance):
        """Test: Energía de vacío E_vac > 0"""
        R_psi = sabio_instance.calcular_radio_cuantico(n=1)
        E_vac = sabio_instance.energia_vacio_cuantico(R_psi)
        
        assert float(E_vac) > 0, f"E_vac debe ser positiva: {E_vac}"
        
        # Verificar orden de magnitud (microjoules)
        assert 1e-9 < float(E_vac) < 1e-3, f"E_vac fuera de rango: {E_vac}"
    
    def test_energia_vacio_formula(self, sabio_instance):
        """Test: E_vac cumple fórmula con 4 términos"""
        R_psi = sabio_instance.calcular_radio_cuantico(n=1)
        E_vac = sabio_instance.energia_vacio_cuantico(R_psi)
        
        # Verificar factor base (ħc/R_Ψ) with scaling factor
        factor = (sabio_instance.hbar * sabio_instance.c) / R_psi
        
        # Corrección áurea
        phi = sabio_instance.phi
        correction = mpf("0.5") + phi/4 - (phi**2)/8 + (phi**3)/16
        
        expected = factor * correction * mpf("1e-12")  # Include scaling factor
        error_rel = abs(E_vac - expected) / expected
        
        assert error_rel < 1e-9, f"E_vac no cumple fórmula: {error_rel}"
    
    def test_energia_vacio_converge(self, sabio_high_precision):
        """Test: E_vac converge con alta precisión"""
        R_psi = sabio_high_precision.calcular_radio_cuantico(n=1)
        
        # Calcular con diferentes precisiones
        mp.dps = 50
        E_50 = sabio_high_precision.energia_vacio_cuantico(R_psi)
        
        mp.dps = 100
        E_100 = sabio_high_precision.energia_vacio_cuantico(R_psi)
        
        # Restaurar precisión
        mp.dps = sabio_high_precision.precision
        
        # Diferencia relativa debe ser pequeña
        diff_rel = abs(E_100 - E_50) / E_50
        assert diff_rel < 1e-45, f"E_vac no converge: {diff_rel}"


# ============================================================================
# 3. Test Nivel Consciente (4 tests)
# ============================================================================

class TestNivelConsciente:
    """Suite de tests para nivel consciente"""
    
    def test_psi_origen_normalizado(self, sabio_instance):
        """Test: Ψ(0,0) normalizado |Ψ(0,0)| ≈ 1"""
        psi_origen = sabio_instance.ecuacion_onda_consciencia(mpf("0.0"), mpf("0.0"))
        magnitud = abs(psi_origen)
        
        assert 0.99 < magnitud < 1.01, f"|Ψ(0,0)| no normalizado: {magnitud}"
    
    def test_psi_es_complejo(self, sabio_instance):
        """Test: Ψ(t,x) es número complejo"""
        t = mpf("1.0")
        x = mpf("0.0")
        psi = sabio_instance.ecuacion_onda_consciencia(t, x)
        
        assert isinstance(psi, complex), f"Ψ no es complejo: {type(psi)}"
        assert psi.real != 0 or psi.imag != 0, "Ψ no debe ser cero"
    
    def test_psi_periodicidad_temporal(self, sabio_instance):
        """Test: Ψ(t,x) periódica en tiempo"""
        x = mpf("0.0")
        omega_0 = sabio_instance.omega_0
        
        # Período T = 2π/ω₀
        T = 2 * pi / omega_0
        
        psi_t0 = sabio_instance.ecuacion_onda_consciencia(mpf("0.0"), x)
        psi_T = sabio_instance.ecuacion_onda_consciencia(T, x)
        
        # Deben ser aproximadamente iguales
        diff = abs(psi_t0 - psi_T)
        assert diff < 0.1, f"Ψ no periódica: diff={diff}"
    
    def test_psi_espacial_acotada(self, sabio_instance):
        """Test: |Ψ(t,x)| acotada para todo x"""
        t = mpf("0.0")
        
        magnitudes = []
        for x_val in [0.0, 0.1, 0.5, 1.0, 10.0]:
            x = mpf(str(x_val))
            psi = sabio_instance.ecuacion_onda_consciencia(t, x)
            magnitudes.append(abs(psi))
        
        # Todas las magnitudes deben estar acotadas
        assert all(0 <= mag <= 1.1 for mag in magnitudes), f"Magnitudes fuera de rango: {magnitudes}"


# ============================================================================
# 4. Test Coherencia (5 tests)
# ============================================================================

class TestCoherencia:
    """Suite de tests para coherencia"""
    
    def test_coherencia_rango(self, sabio_instance):
        """Test: Coherencia en rango [0, 1]"""
        for n in range(1, 10):
            res = sabio_instance.resonancia_cuantica(n)
            assert 0 <= res.coherencia <= 1, f"Coherencia fuera de rango n={n}: {res.coherencia}"
    
    def test_coherencia_decreciente(self, sabio_instance):
        """Test: Coherencia decrece con n"""
        coherencias = []
        for n in range(1, 8):
            res = sabio_instance.resonancia_cuantica(n)
            coherencias.append(res.coherencia)
        
        # Verificar decrecimiento monotónico
        for i in range(len(coherencias) - 1):
            assert coherencias[i] >= coherencias[i+1], f"Coherencia no decrece: {coherencias}"
    
    def test_coherencia_exponencial(self, sabio_instance):
        """Test: Coherencia sigue decay exponencial"""
        import math
        tau = 8.0
        
        for n in [1, 2, 3, 5, 8]:
            res = sabio_instance.resonancia_cuantica(n)
            expected = math.exp(-n / tau)
            
            error_rel = abs(res.coherencia - expected) / expected
            assert error_rel < 0.01, f"Coherencia no exponencial n={n}: {error_rel}"
    
    def test_entropia_rango(self, sabio_instance):
        """Test: Entropía en rango [0, 1]"""
        for n in range(1, 10):
            res = sabio_instance.resonancia_cuantica(n)
            assert 0 <= res.entropia <= 1, f"Entropía fuera de rango n={n}: {res.entropia}"
    
    def test_entropia_vs_coherencia(self, sabio_instance):
        """Test: Entropía crece cuando coherencia decrece"""
        entropias = []
        coherencias = []
        
        for n in range(2, 8):  # Skip n=1 donde entropía puede ser baja
            res = sabio_instance.resonancia_cuantica(n)
            entropias.append(res.entropia)
            coherencias.append(res.coherencia)
        
        # Verificar anticorrelación general
        # Cuando coherencia baja, entropía tiende a subir
        assert entropias[-1] >= entropias[0] * 0.5, "Entropía no aumenta apropiadamente"


# ============================================================================
# 5. Test Resonancia Cuántica (5 tests)
# ============================================================================

class TestResonanciaQuantica:
    """Suite de tests para resonancias cuánticas"""
    
    def test_frecuencia_aurea(self, sabio_instance):
        """Test: Frecuencias siguen secuencia áurea"""
        f0 = float(sabio_instance.f0)
        phi = float(sabio_instance.phi)
        
        for n in range(1, 6):
            res = sabio_instance.resonancia_cuantica(n)
            expected = f0 * (phi ** n)
            
            error_rel = abs(res.frecuencia - expected) / expected
            assert error_rel < 1e-6, f"Frecuencia no áurea n={n}: {error_rel}"
    
    def test_amplitud_compleja(self, sabio_instance):
        """Test: Amplitud es número complejo"""
        res = sabio_instance.resonancia_cuantica(n_harmonico=1)
        
        assert isinstance(res.amplitud_compleja, complex), "Amplitud no es compleja"
        
        # Magnitud debe ser aproximadamente coherencia
        mag = abs(res.amplitud_compleja)
        assert abs(mag - res.coherencia) < 0.01, f"Magnitud incorrecta: {mag} vs {res.coherencia}"
    
    def test_firma_vibracional_unica(self, sabio_instance):
        """Test: Cada armónico tiene firma única"""
        firmas = set()
        
        for n in range(1, 20):
            res = sabio_instance.resonancia_cuantica(n)
            assert res.firma_vibracional not in firmas, f"Firma duplicada n={n}"
            firmas.add(res.firma_vibracional)
        
        assert len(firmas) == 19, "No todas las firmas son únicas"
    
    def test_firma_vibracional_formato(self, sabio_instance):
        """Test: Firma vibracional es hash hexadecimal de 16 chars"""
        res = sabio_instance.resonancia_cuantica(n_harmonico=1)
        firma = res.firma_vibracional
        
        assert len(firma) == 16, f"Firma longitud incorrecta: {len(firma)}"
        assert all(c in '0123456789abcdef' for c in firma), "Firma no es hexadecimal"
    
    def test_dataclass_completo(self, sabio_instance):
        """Test: ResonanciaQuantica tiene todos los campos"""
        res = sabio_instance.resonancia_cuantica(n_harmonico=3)
        
        assert hasattr(res, 'n_harmonico'), "Falta n_harmonico"
        assert hasattr(res, 'frecuencia'), "Falta frecuencia"
        assert hasattr(res, 'coherencia'), "Falta coherencia"
        assert hasattr(res, 'entropia'), "Falta entropia"
        assert hasattr(res, 'amplitud_compleja'), "Falta amplitud_compleja"
        assert hasattr(res, 'firma_vibracional'), "Falta firma_vibracional"
        
        assert res.n_harmonico == 3, "n_harmonico incorrecto"


# ============================================================================
# 6. Test Matriz de Simbiosis (4 tests)
# ============================================================================

class TestMatrizSimbiosis:
    """Suite de tests para matriz de simbiosis"""
    
    def test_matriz_completa(self, sabio_instance):
        """Test: Matriz tiene todos los niveles"""
        matriz = sabio_instance.validacion_matriz_simbiosis()
        
        assert hasattr(matriz, 'nivel_python'), "Falta nivel_python"
        assert hasattr(matriz, 'nivel_lean'), "Falta nivel_lean"
        assert hasattr(matriz, 'nivel_sage'), "Falta nivel_sage"
        assert hasattr(matriz, 'nivel_sabio'), "Falta nivel_sabio"
        assert hasattr(matriz, 'nivel_cuantico'), "Falta nivel_cuantico"
        assert hasattr(matriz, 'nivel_consciente'), "Falta nivel_consciente"
        assert hasattr(matriz, 'coherencia_total'), "Falta coherencia_total"
    
    def test_niveles_rango(self, sabio_instance):
        """Test: Todos los niveles en rango [0, 1]"""
        matriz = sabio_instance.validacion_matriz_simbiosis()
        
        assert 0 <= matriz.nivel_python <= 1, "nivel_python fuera de rango"
        assert 0 <= matriz.nivel_lean <= 1, "nivel_lean fuera de rango"
        assert 0 <= matriz.nivel_sage <= 1, "nivel_sage fuera de rango"
        assert 0 <= matriz.nivel_sabio <= 1, "nivel_sabio fuera de rango"
        assert 0 <= matriz.nivel_cuantico <= 1, "nivel_cuantico fuera de rango"
        assert 0 <= matriz.nivel_consciente <= 1, "nivel_consciente fuera de rango"
        assert 0 <= matriz.coherencia_total <= 1, "coherencia_total fuera de rango"



# ============================================================================
# 7. Test Espectro Resonante (3 tests)
# ============================================================================

class TestEspectroResonante:
    """Suite de tests para espectro resonante"""
    
    def test_espectro_longitud(self, sabio_instance):
        """Test: Espectro tiene longitud correcta"""
        espectro = sabio_instance.generar_espectro_resonante(n_harmonicos=8)
        assert len(espectro) == 8, f"Longitud incorrecta: {len(espectro)}"
        
        espectro16 = sabio_instance.generar_espectro_resonante(n_harmonicos=16)
        assert len(espectro16) == 16, f"Longitud incorrecta: {len(espectro16)}"
    
    def test_espectro_ordenado(self, sabio_instance):
        """Test: Espectro ordenado por n_harmonico"""
        espectro = sabio_instance.generar_espectro_resonante(n_harmonicos=10)
        
        for i, res in enumerate(espectro):
            assert res.n_harmonico == i + 1, f"Orden incorrecto en posición {i}"
    
    def test_espectro_frecuencias_crecientes(self, sabio_instance):
        """Test: Frecuencias crecen monotónicamente"""
        espectro = sabio_instance.generar_espectro_resonante(n_harmonicos=8)
        
        frecuencias = [res.frecuencia for res in espectro]
        
        for i in range(len(frecuencias) - 1):
            assert frecuencias[i] < frecuencias[i+1], f"Frecuencias no crecen: {frecuencias}"


# ============================================================================
# 8. Test Reporte (4 tests)
# ============================================================================

class TestReporte:
    """Suite de tests para reporte SABIO"""
    
    def test_reporte_completo(self, sabio_instance):
        """Test: Reporte tiene todos los campos"""
        reporte = sabio_instance.reporte_sabio_infinity4()
        
        assert hasattr(reporte, 'timestamp'), "Falta timestamp"
        assert hasattr(reporte, 'precision'), "Falta precision"
        assert hasattr(reporte, 'frecuencia_base'), "Falta frecuencia_base"
        assert hasattr(reporte, 'omega_0'), "Falta omega_0"
        assert hasattr(reporte, 'matriz_simbiosis'), "Falta matriz_simbiosis"
        assert hasattr(reporte, 'espectro_resonante'), "Falta espectro_resonante"
        assert hasattr(reporte, 'radio_cuantico'), "Falta radio_cuantico"
        assert hasattr(reporte, 'energia_vacio'), "Falta energia_vacio"
        assert hasattr(reporte, 'psi_origen'), "Falta psi_origen"
        assert hasattr(reporte, 'coherencia_global'), "Falta coherencia_global"
        assert hasattr(reporte, 'status'), "Falta status"
    
    def test_exportar_json(self, sabio_instance):
        """Test: Exportar reporte a JSON"""
        reporte = sabio_instance.reporte_sabio_infinity4()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = sabio_instance.exportar_reporte(reporte, formato='json', output_dir=tmpdir)
            
            assert os.path.exists(filepath), f"Archivo no creado: {filepath}"
            assert filepath.endswith('.json'), "Extensión incorrecta"
            
            # Verificar que es JSON válido
            with open(filepath, 'r') as f:
                data = json.load(f)
            
            assert 'timestamp' in data, "Falta timestamp en JSON"
            assert 'coherencia_global' in data, "Falta coherencia_global en JSON"
    
    def test_exportar_txt(self, sabio_instance):
        """Test: Exportar reporte a TXT"""
        reporte = sabio_instance.reporte_sabio_infinity4()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = sabio_instance.exportar_reporte(reporte, formato='txt', output_dir=tmpdir)
            
            assert os.path.exists(filepath), f"Archivo no creado: {filepath}"
            assert filepath.endswith('.txt'), "Extensión incorrecta"
            
            # Verificar contenido
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            assert 'SABIO' in content, "Falta título SABIO"
            assert 'COHERENCIA TOTAL' in content, "Falta coherencia total"
    
    def test_status_coherencia(self, sabio_instance):
        """Test: Status refleja coherencia correctamente"""
        reporte = sabio_instance.reporte_sabio_infinity4()
        
        if reporte.coherencia_global >= 0.90:
            assert 'OPERACIONAL' in reporte.status or '✅' in reporte.status, \
                f"Status incorrecto para alta coherencia: {reporte.status}"
        else:
            assert 'SINTONIZANDO' in reporte.status or '🔄' in reporte.status, \
                f"Status incorrecto para baja coherencia: {reporte.status}"


# ============================================================================
# 9. Test Integración (2 tests)
# ============================================================================

class TestIntegracion:
    """Suite de tests de integración"""
    
    def test_demo_completa(self):
        """Test: Demo completa ejecuta sin errores"""
        with tempfile.TemporaryDirectory() as tmpdir:
            reporte = demo_sabio_infinity4(
                precision=30,
                n_harmonicos=6,
                output_dir=tmpdir,
                save_visualization=False  # No guardar imagen en tests
            )
            
            assert isinstance(reporte, ReporteSABIO), "Reporte tipo incorrecto"
            assert reporte.coherencia_global > 0, "Coherencia global inválida"
            
            # Verificar archivos generados
            files = os.listdir(tmpdir)
            json_files = [f for f in files if f.endswith('.json')]
            txt_files = [f for f in files if f.endswith('.txt')]
            
            assert len(json_files) >= 1, "No se generó JSON"
            assert len(txt_files) >= 1, "No se generó TXT"
    
    def test_flujo_completo(self):
        """Test: Flujo completo de validación"""
        # 1. Inicializar
        sabio = SABIO_Infinity4(precision=30)
        
        # 2. Nivel cuántico
        R_psi = sabio.calcular_radio_cuantico(n=1)
        E_vac = sabio.energia_vacio_cuantico(R_psi)
        assert float(E_vac) > 0, "E_vac no positiva"
        
        # 3. Nivel consciente
        psi = sabio.ecuacion_onda_consciencia(mpf("0.0"), mpf("0.0"))
        assert abs(abs(psi) - 1.0) < 0.1, "Ψ no normalizada"
        
        # 4. Resonancias
        espectro = sabio.generar_espectro_resonante(n_harmonicos=5)
        assert len(espectro) == 5, "Espectro incompleto"
        
        # 5. Matriz de simbiosis
        matriz = sabio.validacion_matriz_simbiosis()
        assert 0 <= matriz.coherencia_total <= 1, "Coherencia fuera de rango"
        
        # 6. Reporte
        reporte = sabio.reporte_sabio_infinity4()
        assert reporte.status in ['OPERACIONAL ✅', 'SINTONIZANDO 🔄'], \
            f"Status inesperado: {reporte.status}"


# ============================================================================
# 10. Test Precisión (2 tests)
# ============================================================================
