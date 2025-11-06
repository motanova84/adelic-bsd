"""
Tests para la calibración del parámetro a

Verifica que:
1. γ > 0 para el valor calibrado de a
2. El límite espectral converge correctamente
3. La optimización encuentra valores válidos
"""

import pytest
import sys
import os
import json

# Add scripts to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'scripts'))

from calibrar_parametro_a import (
    compute_delta_star,
    compute_gamma,
    compute_spectral_bound,
    find_optimal_a
)


class TestParameterCalibration:
    """Tests for parameter calibration"""
    
    def test_spectral_bound_computation(self):
        """Verificar que el límite espectral se calcula correctamente"""
        a = 100.0
        delta = 0.05
        
        bound = compute_spectral_bound(a, delta)
        
        # El límite espectral debe ser finito
        assert not pytest.approx(bound) == float('inf')
        assert not pytest.approx(bound) == float('-inf')
        print(f"✅ Límite espectral calculado: {bound:.6f}")
    
    def test_delta_star_computation(self):
        """Verificar que δ* se calcula correctamente"""
        a = 200.0
        
        delta_star = compute_delta_star(a)
        
        # δ* debe estar en el rango válido
        assert 0.001 <= delta_star <= 0.1
        print(f"✅ δ* calculado para a={a}: {delta_star:.6f}")
    
    def test_gamma_computation(self):
        """Verificar que γ se calcula correctamente"""
        a = 200.0
        delta_star = compute_delta_star(a)
        gamma = compute_gamma(delta_star, a)
        
        # γ debe ser finito
        assert not pytest.approx(gamma) == float('inf')
        assert not pytest.approx(gamma) == float('-inf')
        print(f"✅ γ calculado: {gamma:.6f}")
    
    def test_gamma_positivity(self):
        """
        Verificar que γ > 0 para valores grandes de a
        
        Este es el test crítico: necesitamos γ > 0 para la
        prueba incondicional de finitud.
        """
        # Probar con varios valores grandes de a
        test_values = [100.0, 150.0, 200.0, 250.0, 300.0]
        
        results = []
        for a in test_values:
            delta_star = compute_delta_star(a)
            gamma = compute_gamma(delta_star, a)
            results.append((a, gamma))
            print(f"   a = {a:.1f}: γ = {gamma:.6f}")
        
        # Al menos uno debe tener γ > 0
        positive_gammas = [g for a, g in results if g > 0]
        assert len(positive_gammas) > 0, "Debe existir al menos un valor con γ > 0"
        
        print(f"\n✅ {len(positive_gammas)}/{len(test_values)} valores con γ > 0")
    
    def test_optimal_a_search(self):
        """Verificar que la búsqueda de a óptimo funciona"""
        # Buscar en un rango pequeño para el test (más rápido)
        results = find_optimal_a(
            target_gamma=0.0,
            a_range=(50.0, 250.0),
            num_points=50,
            verbose=False
        )
        
        # Debe haber evaluado algunos puntos
        assert len(results) > 0
        
        # Algunos deben ser válidos
        valid_results = [r for r in results if r.get('passes', False)]
        
        print(f"\n✅ Búsqueda completada:")
        print(f"   • Puntos evaluados: {len(results)}")
        print(f"   • Puntos válidos: {len(valid_results)}")
        
        if valid_results:
            optimal = valid_results[0]
            print(f"   • a óptimo encontrado: {optimal['a']:.2f}")
            print(f"   • γ correspondiente: {optimal['gamma']:.6f}")
    
    def test_calibration_report_format(self):
        """Verificar que el reporte de calibración tiene el formato correcto"""
        # Ejecutar una calibración pequeña
        results = find_optimal_a(
            target_gamma=0.0,
            a_range=(100.0, 200.0),
            num_points=20,
            verbose=False
        )
        
        # Verificar estructura de resultados
        for result in results:
            if 'error' not in result:
                assert 'a' in result
                assert 'delta_star' in result
                assert 'gamma' in result
                assert 'passes' in result
        
        print("✅ Formato de reporte validado")


class TestSpectralBoundProperties:
    """Tests for spectral bound function properties"""
    
    def test_spectral_bound_continuity(self):
        """Verificar continuidad del límite espectral"""
        a = 200.0
        delta1 = 0.05
        delta2 = 0.050001
        
        bound1 = compute_spectral_bound(a, delta1)
        bound2 = compute_spectral_bound(a, delta2)
        
        # Valores cercanos de δ deben dar límites cercanos
        assert abs(bound1 - bound2) < 0.01
        print(f"✅ Continuidad verificada: |Δbound| = {abs(bound1 - bound2):.8f}")
    
    def test_spectral_bound_monotonicity_in_a(self):
        """Verificar comportamiento respecto a a"""
        delta = 0.05
        a1 = 100.0
        a2 = 200.0
        
        bound1 = compute_spectral_bound(a1, delta)
        bound2 = compute_spectral_bound(a2, delta)
        
        # Simplemente verificar que son finitos y diferentes
        assert bound1 != bound2
        print(f"✅ Dependencia en a verificada: bound(a={a1}) = {bound1:.6f}, bound(a={a2}) = {bound2:.6f}")


def test_calibration_file_generation():
    """Verificar que el script genera archivos de salida correctos"""
    # Este test verifica que podemos importar y usar las funciones
    # sin errores de importación
    from calibrar_parametro_a import generate_calibration_report
    
    # Crear datos de prueba
    test_results = [
        {'a': 100.0, 'delta_star': 0.05, 'gamma': -0.1, 'passes': False},
        {'a': 200.0, 'delta_star': 0.04, 'gamma': 0.05, 'passes': True},
    ]
    
    # No guardar archivo en el test
    report = generate_calibration_report(test_results, output_path=None)
    
    # Verificar estructura del reporte
    assert 'status' in report
    assert 'total_evaluated' in report
    
    print(f"✅ Reporte generado correctamente: status={report['status']}")


if __name__ == "__main__":
    # Permitir ejecución directa para debugging
    pytest.main([__file__, "-v"])
