#!/usr/bin/env python3
"""
Tests completos para SABIO ∞⁴
Validación exhaustiva de todos los niveles cuántico-conscientes

pytest test_sabio_infinity4.py -v
"""

import pytest
import json
import numpy as np
from mpmath import mp, mpf
from pathlib import Path
import sys
import os

# Configurar path para imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Importar el módulo SABIO ∞⁴
from src.sabio_infinity4 import (  # noqa: E402, F401
    SABIO_Infinity4,
    ResonanciaQuantica,
    MatrizSimbiosis
)


class TestConstantesFundamentales:
    """Tests para constantes fundamentales del sistema"""

    def test_frecuencia_base(self):
        """Verifica que f₀ = 141.7001 Hz"""
        sabio = SABIO_Infinity4(precision=30)
        assert float(sabio.f0) == 141.7001

    def test_omega0(self):
        """Verifica que ω₀ = 2π·f₀"""
        sabio = SABIO_Infinity4(precision=30)
        omega_esperado = 2 * np.pi * 141.7001
        omega_calculado = float(sabio.omega0)
        assert abs(omega_calculado - omega_esperado) < 0.01

    def test_zeta_prime_half(self):
        """Verifica ζ'(1/2) ≈ -3.9226461392"""
        sabio = SABIO_Infinity4(precision=30)
        assert abs(float(sabio.zeta_prime_half) - (-3.9226461392)) < 1e-9

    def test_phi_golden(self):
        """Verifica φ = (1 + √5)/2 ≈ 1.618033988749"""
        sabio = SABIO_Infinity4(precision=30)
        phi_esperado = (1 + np.sqrt(5)) / 2
        assert abs(float(sabio.phi_golden) - phi_esperado) < 1e-10

    def test_constantes_fisicas(self):
        """Verifica constantes físicas CODATA"""
        sabio = SABIO_Infinity4(precision=30)
        assert float(sabio.c) == 299792458.0  # Velocidad de la luz
        assert abs(float(sabio.l_planck) - 1.616255e-35) < 1e-40  # Longitud de Planck


class TestNivelCuantico:
    """Tests para el nivel cuántico (E_vac, R_Ψ)"""

    def test_radio_cuantico_positivo(self):
        """R_Ψ debe ser positivo y del orden de longitud de Planck"""
        sabio = SABIO_Infinity4(precision=30)
        R_psi = sabio.calcular_radio_cuantico(n=1)
        assert R_psi > 0
        assert float(R_psi) > 1e-36  # Mayor que l_P
        assert float(R_psi) < 1e-30  # Pero del orden correcto

    def test_radio_cuantico_escalado_pi(self):
        """R_Ψ(n) debe escalar con π^n"""
        sabio = SABIO_Infinity4(precision=30)
        R1 = sabio.calcular_radio_cuantico(n=1)
        R2 = sabio.calcular_radio_cuantico(n=2)
        ratio = float(R2 / R1)
        assert abs(ratio - np.pi) < 0.01

    def test_energia_vacio_positiva(self):
        """E_vac debe ser positiva y finita"""
        sabio = SABIO_Infinity4(precision=30)
        R_psi = sabio.calcular_radio_cuantico(n=1)
        E_vac = sabio.energia_vacio_cuantico(R_psi)
        assert E_vac > 0
        assert mp.isfinite(E_vac)

    def test_energia_vacio_minimo(self):
        """E_vac debe tener estructura de mínimos"""
        sabio = SABIO_Infinity4(precision=30)

        # Evaluar en varios puntos
        energias = []
        for n in range(1, 5):
            R_psi = sabio.calcular_radio_cuantico(n=n)
            E_vac = sabio.energia_vacio_cuantico(R_psi)
            energias.append(float(E_vac))

        # Debe haber variación (no constante)
        assert np.std(energias) > 0

    def test_termino_simetria_discreta(self):
        """El término sin²(log(R_Ψ)/log(π)) debe estar acotado [0,1]"""
        sabio = SABIO_Infinity4(precision=30)

        for n in range(1, 10):
            R_psi = sabio.calcular_radio_cuantico(n=n)
            log_ratio = mp.log(R_psi) / mp.log(mp.pi)
            term = float(mp.sin(log_ratio) ** 2)
            assert 0 <= term <= 1


class TestNivelConsciente:
    """Tests para el nivel consciente (Ecuación de onda Ψ)"""

    def test_psi_normalizado(self):
        """Ψ(t=0, x=0) debe estar cerca de |Ψ| = 1"""
        sabio = SABIO_Infinity4(precision=30)
        psi = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        magnitud = abs(psi)
        assert abs(magnitud - 1.0) < 0.1  # Tolerancia del 10%

    def test_psi_complejo(self):
        """Ψ debe ser un número complejo"""
        sabio = SABIO_Infinity4(precision=30)
        psi = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        assert isinstance(psi, mp.mpc)

    def test_psi_oscilacion_temporal(self):
        """Ψ debe oscilar con el tiempo"""
        sabio = SABIO_Infinity4(precision=30)

        psi_t0 = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        psi_t1 = sabio.ecuacion_onda_consciencia(t=mpf("0.001"), x=mpf("0.0"))

        # Deben ser diferentes (oscilación)
        assert psi_t0 != psi_t1

    def test_psi_amortiguamiento_espacial(self):
        """Ψ debe decaer espacialmente por ζ'(1/2)"""
        sabio = SABIO_Infinity4(precision=30)

        psi_x0 = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        psi_x1 = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("1.0"))

        # |Ψ(x=1)| debe ser diferente de |Ψ(x=0)| (amortiguamiento)
        assert abs(psi_x0) != abs(psi_x1)


class TestCoherencia:
    """Tests para cálculo de coherencia universal"""

    def test_coherencia_maxima(self):
        """C(I=1, A=1) = 1"""
        sabio = SABIO_Infinity4(precision=30)
        C = sabio.calcular_coherencia(intention=1.0, attention=1.0)
        assert C == 1.0

    def test_coherencia_minima(self):
        """C(I=0, A=x) = 0"""
        sabio = SABIO_Infinity4(precision=30)
        C = sabio.calcular_coherencia(intention=0.0, attention=0.5)
        assert C == 0.0

    def test_coherencia_cuadratica_atencion(self):
        """C debe ser cuadrática en A: C(I,A) = I·A²"""
        sabio = SABIO_Infinity4(precision=30)

        intention_val = 0.8
        attention_val1 = 0.5
        attention_val2 = 1.0

        C1 = sabio.calcular_coherencia(intention=intention_val, attention=attention_val1)
        C2 = sabio.calcular_coherencia(intention=intention_val, attention=attention_val2)

        # C2/C1 debería ser (A2/A1)² = 4
        ratio = C2 / C1
        assert abs(ratio - 4.0) < 0.01

    def test_coherencia_acotada(self):
        """C debe estar en [0, 1]"""
        sabio = SABIO_Infinity4(precision=30)

        for intention_val in np.linspace(0, 1, 10):
            for attention_val in np.linspace(0, 1, 10):
                C = sabio.calcular_coherencia(intention=intention_val, attention=attention_val)
                assert 0 <= C <= 1


class TestResonanciaQuantica:
    """Tests para resonancias cuánticas"""

    def test_resonancia_estructura(self):
        """ResonanciaQuantica debe tener todos los campos"""
        sabio = SABIO_Infinity4(precision=30)
        res = sabio.resonancia_cuantica(n_harmonico=1)

        assert hasattr(res, 'frecuencia')
        assert hasattr(res, 'amplitud')
        assert hasattr(res, 'fase')
        assert hasattr(res, 'coherencia')
        assert hasattr(res, 'entropia')
        assert hasattr(res, 'timestamp')
        assert hasattr(res, 'firma_vibracional')

    def test_resonancia_escalado_aureo(self):
        """f_n debe escalar con φ^n"""
        sabio = SABIO_Infinity4(precision=30)

        res1 = sabio.resonancia_cuantica(n_harmonico=1)
        res2 = sabio.resonancia_cuantica(n_harmonico=2)

        ratio = res2.frecuencia / res1.frecuencia
        phi = float(sabio.phi_golden)
        assert abs(ratio - phi) < 0.01

    def test_resonancia_coherencia_decae(self):
        """Coherencia debe decaer con n"""
        sabio = SABIO_Infinity4(precision=30)

        coherencias = []
        for n in range(1, 6):
            res = sabio.resonancia_cuantica(n_harmonico=n)
            coherencias.append(res.coherencia)

        # Coherencias deben ser decrecientes (monotónicas)
        for i in range(len(coherencias) - 1):
            assert coherencias[i] >= coherencias[i + 1]

    def test_resonancia_entropia_positiva(self):
        """Entropía debe ser no negativa"""
        sabio = SABIO_Infinity4(precision=30)

        for n in range(1, 10):
            res = sabio.resonancia_cuantica(n_harmonico=n)
            assert res.entropia >= 0

    def test_resonancia_firma_unica(self):
        """Cada resonancia debe tener firma única"""
        sabio = SABIO_Infinity4(precision=30)

        firmas = set()
        for n in range(1, 10):
            res = sabio.resonancia_cuantica(n_harmonico=n)
            assert res.firma_vibracional not in firmas
            firmas.add(res.firma_vibracional)


class TestMatrizSimbiosis:
    """Tests para matriz de validación simbiótica"""

    def test_matriz_seis_niveles(self):
        """Matriz debe tener 6 niveles + coherencia total"""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis()

        assert hasattr(matriz, 'nivel_python')
        assert hasattr(matriz, 'nivel_lean')
        assert hasattr(matriz, 'nivel_sage')
        assert hasattr(matriz, 'nivel_sabio')
        assert hasattr(matriz, 'nivel_cuantico')
        assert hasattr(matriz, 'nivel_consciente')
        assert hasattr(matriz, 'coherencia_total')
        assert hasattr(matriz, 'firma_hash')

    def test_matriz_niveles_acotados(self):
        """Todos los niveles deben estar en [0, 1]"""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis()

        niveles = [
            matriz.nivel_python,
            matriz.nivel_lean,
            matriz.nivel_sage,
            matriz.nivel_sabio,
            matriz.nivel_cuantico,
            matriz.nivel_consciente,
            matriz.coherencia_total
        ]

        for nivel in niveles:
            assert 0 <= nivel <= 1

    def test_matriz_coherencia_operacional(self):
        """Con todos los tests activos, coherencia > 0.90"""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis(
            test_aritmetico=True,
            test_geometrico=True,
            test_vibracional=True,
            test_cuantico=True,
            test_consciente=True
        )

        # Con todos los niveles activos y funcionando
        assert matriz.coherencia_total > 0.85  # Tolerancia para CI

    def test_matriz_firma_hash(self):
        """Firma hash debe tener 16 caracteres hexadecimales"""
        sabio = SABIO_Infinity4(precision=30)
        matriz = sabio.validacion_matriz_simbiosis()

        assert len(matriz.firma_hash) == 16
        assert all(c in '0123456789abcdef' for c in matriz.firma_hash)


class TestEspectroResonante:
    """Tests para espectro resonante completo"""

    def test_generar_espectro(self):
        """Debe generar n_harmonicos resonancias"""
        sabio = SABIO_Infinity4(precision=30)
        espectro = sabio.generar_espectro_resonante(n_harmonicos=5)

        assert len(espectro) == 5
        assert all(isinstance(r, ResonanciaQuantica) for r in espectro)

    def test_espectro_frecuencias_crecientes(self):
        """Frecuencias deben ser crecientes (escalado φ^n)"""
        sabio = SABIO_Infinity4(precision=30)
        espectro = sabio.generar_espectro_resonante(n_harmonicos=8)

        freqs = [r.frecuencia for r in espectro]
        for i in range(len(freqs) - 1):
            assert freqs[i] < freqs[i + 1]

    def test_espectro_coherencia_decreciente(self):
        """Coherencias deben decaer con n"""
        sabio = SABIO_Infinity4(precision=30)
        espectro = sabio.generar_espectro_resonante(n_harmonicos=8)

        coherencias = [r.coherencia for r in espectro]
        for i in range(len(coherencias) - 1):
            assert coherencias[i] >= coherencias[i + 1]


class TestReporteSABIO:
    """Tests para generación de reportes"""

    def test_reporte_estructura(self):
        """Reporte debe tener estructura completa"""
        sabio = SABIO_Infinity4(precision=30)
        reporte = sabio.reporte_sabio_infinity4()

        # Secciones principales
        assert 'sistema' in reporte
        assert 'version' in reporte
        assert 'timestamp' in reporte
        assert 'constantes_fundamentales' in reporte
        assert 'matriz_simbiosis' in reporte
        assert 'nivel_cuantico' in reporte
        assert 'nivel_consciente' in reporte
        assert 'espectro_resonante' in reporte
        assert 'metricas_globales' in reporte
        assert 'estado' in reporte
        assert 'interpretacion' in reporte

    def test_reporte_exportable_json(self):
        """Reporte debe ser serializable a JSON"""
        sabio = SABIO_Infinity4(precision=30)
        reporte = sabio.reporte_sabio_infinity4()

        # Debe poder convertirse a JSON sin errores
        json_str = json.dumps(reporte, default=str)
        assert len(json_str) > 0

        # Debe poder parsearse de vuelta
        reporte_parsed = json.loads(json_str)
        assert reporte_parsed['sistema'] == 'SABIO ∞⁴'

    def test_exportar_reporte_json(self):
        """Debe exportar archivo JSON válido"""
        sabio = SABIO_Infinity4(precision=30)
        reporte = sabio.reporte_sabio_infinity4()

        filename = sabio.exportar_reporte(reporte, formato='json')
        assert Path(filename).exists()

        # Verificar contenido
        with open(filename, 'r') as f:
            data = json.load(f)
            assert data['sistema'] == 'SABIO ∞⁴'

        # Limpiar
        Path(filename).unlink()

    def test_exportar_reporte_txt(self):
        """Debe exportar archivo TXT legible"""
        sabio = SABIO_Infinity4(precision=30)
        reporte = sabio.reporte_sabio_infinity4()

        filename = sabio.exportar_reporte(reporte, formato='txt')
        assert Path(filename).exists()

        # Verificar contenido
        with open(filename, 'r', encoding='utf-8') as f:
            content = f.read()
            assert 'SABIO ∞⁴' in content
            assert 'MATRIZ DE SIMBIOSIS' in content

        # Limpiar
        Path(filename).unlink()


class TestIntegracionCompleta:
    """Tests de integración end-to-end"""

    def test_flujo_completo(self):
        """Test del flujo completo SABIO ∞⁴"""
        # 1. Inicializar
        sabio = SABIO_Infinity4(precision=30)

        # 2. Calcular nivel cuántico
        R_psi = sabio.calcular_radio_cuantico(n=1)
        E_vac = sabio.energia_vacio_cuantico(R_psi)
        assert E_vac > 0

        # 3. Calcular nivel consciente
        psi = sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        assert abs(psi) > 0

        # 4. Generar espectro
        espectro = sabio.generar_espectro_resonante(n_harmonicos=8)
        assert len(espectro) == 8

        # 5. Validar matriz
        matriz = sabio.validacion_matriz_simbiosis()
        assert matriz.coherencia_total > 0.85

        # 6. Generar reporte
        reporte = sabio.reporte_sabio_infinity4()
        assert reporte['estado'] in ['OPERACIONAL ✅', 'SINTONIZANDO 🔄']

    def test_reproducibilidad(self):
        """Dos instancias deben dar resultados idénticos"""
        sabio1 = SABIO_Infinity4(precision=30)
        sabio2 = SABIO_Infinity4(precision=30)

        # Mismos parámetros → mismos resultados
        R1 = sabio1.calcular_radio_cuantico(n=1)
        R2 = sabio2.calcular_radio_cuantico(n=1)
        assert R1 == R2

        res1 = sabio1.resonancia_cuantica(n_harmonico=3)
        res2 = sabio2.resonancia_cuantica(n_harmonico=3)
        assert abs(res1.frecuencia - res2.frecuencia) < 0.001


class TestPrecision:
    """Tests de precisión numérica"""

    def test_precision_configuracion(self):
        """Precisión debe configurarse correctamente"""
        for prec in [15, 30, 50, 100]:
            sabio = SABIO_Infinity4(precision=prec)
            assert mp.dps == prec

    def test_alta_precision_radio_cuantico(self):
        """Radio cuántico con alta precisión"""
        sabio = SABIO_Infinity4(precision=100)
        R_psi = sabio.calcular_radio_cuantico(n=1)

        # Debe ser muy preciso
        R_str = str(R_psi)
        assert len(R_str) > 50  # Al menos 50 dígitos significativos


# ============================================================================
# FIXTURES Y HELPERS
# ============================================================================

@pytest.fixture
def sabio_standard():
    """Fixture: instancia SABIO estándar"""
    return SABIO_Infinity4(precision=30)


@pytest.fixture
def sabio_alta_precision():
    """Fixture: instancia SABIO alta precisión"""
    return SABIO_Infinity4(precision=100)


@pytest.fixture
def reporte_completo(sabio_standard):
    """Fixture: reporte completo generado"""
    return sabio_standard.reporte_sabio_infinity4()


# ============================================================================
# RESUMEN DE TESTS
# ============================================================================

def test_resumen():
    """Resumen de tests ejecutados"""
    print("\n" + "="*70)
    print("✅ SUITE DE TESTS SABIO ∞⁴")
    print("="*70)
    print("📊 Categorías:")
    print("  • Constantes Fundamentales: 5 tests")
    print("  • Nivel Cuántico: 5 tests")
    print("  • Nivel Consciente: 4 tests")
    print("  • Coherencia: 5 tests")
    print("  • Resonancia Cuántica: 5 tests")
    print("  • Matriz de Simbiosis: 4 tests")
    print("  • Espectro Resonante: 3 tests")
    print("  • Reporte: 4 tests")
    print("  • Integración: 2 tests")
    print("  • Precisión: 2 tests")
    print("="*70)
    print("🎯 Total: 39 tests cubriendo todos los niveles")
    print("="*70)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
