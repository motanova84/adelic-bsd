#!/usr/bin/env python3
"""
Calibración automática y validación cruzada del parámetro a
con múltiples métodos independientes
"""

import numpy as np
from scipy.optimize import minimize_scalar, differential_evolution
import json
from pathlib import Path


class CompleteCalibratorValidator:
    """Calibra y valida a con 3 métodos independientes"""
    
    # Constants for optimization parameters
    GAMMA_TARGET = 0.01  # Target gamma value for global search
    PENALTY_WEIGHT = 100  # Penalty weight for gamma deviation
    MONTE_CARLO_SAMPLES = 10000  # Number of Monte Carlo sampling iterations
    
    def __init__(self):
        self.zeta_prime_half = -1.460354508
        self.methods = {
            'gradient': self._method_gradient,
            'global_search': self._method_global,
            'bootstrap': self._method_bootstrap
        }
    
    def _spectral_bound(self, a, delta):
        """
        Función espectral completa
        F(a,δ) = a·exp(-δ²/σ²) · |ζ'(1/2)|
        """
        sigma = 0.05
        return a * np.exp(-delta**2 / sigma**2) * abs(self.zeta_prime_half)
    
    def _compute_gamma(self, a, delta):
        """Segunda derivada (convexidad)"""
        eps = 1e-8
        f_center = self._spectral_bound(a, delta)
        f_plus = self._spectral_bound(a, delta + eps)
        f_minus = self._spectral_bound(a, delta - eps)
        
        gamma = (f_plus - 2*f_center + f_minus) / (eps**2)
        return gamma
    
    def _method_gradient(self):
        """Método 1: Optimización por gradiente"""
        def objective(a):
            # Encontrar δ* óptimo
            result = minimize_scalar(
                lambda d: -self._spectral_bound(a, d),
                bounds=(0.001, 0.15),
                method='bounded'
            )
            delta_star = result.x
            gamma = self._compute_gamma(a, delta_star)
            
            # Penalizar si γ < 0
            if gamma <= 0:
                return 1e10
            return a  # Minimizar a (queremos el mínimo a válido)
        
        result = minimize_scalar(
            objective,
            bounds=(1, 1000),
            method='bounded'
        )
        
        a_opt = result.x
        
        # Recalcular δ* y γ
        result_delta = minimize_scalar(
            lambda d: -self._spectral_bound(a_opt, d),
            bounds=(0.001, 0.15),
            method='bounded'
        )
        delta_star = result_delta.x
        gamma = self._compute_gamma(a_opt, delta_star)
        
        return {
            'a': a_opt,
            'delta_star': delta_star,
            'gamma': gamma,
            'method': 'gradient'
        }
    
    def _method_global(self):
        """Método 2: Búsqueda global evolutiva"""
        def objective(params):
            a = params[0]
            delta = params[1]
            
            gamma = self._compute_gamma(a, delta)
            
            if gamma <= 0:
                return 1e10
            
            # Minimizar a + penalizar desviación de γ de target
            return a + self.PENALTY_WEIGHT * abs(gamma - self.GAMMA_TARGET)
        
        bounds = [(1, 1000), (0.001, 0.15)]
        
        result = differential_evolution(
            objective,
            bounds,
            seed=42,
            maxiter=1000
        )
        
        a_opt, delta_opt = result.x
        gamma = self._compute_gamma(a_opt, delta_opt)
        
        return {
            'a': a_opt,
            'delta_star': delta_opt,
            'gamma': gamma,
            'method': 'global_search'
        }
    
    def _method_bootstrap(self):
        """Método 3: Bootstrap con muestreo Monte Carlo"""
        np.random.seed(42)
        
        valid_configs = []
        
        # Muestreo Monte Carlo
        for _ in range(self.MONTE_CARLO_SAMPLES):
            a = np.random.uniform(1, 1000)
            delta = np.random.uniform(0.001, 0.15)
            
            gamma = self._compute_gamma(a, delta)
            
            if gamma > 0:
                valid_configs.append({
                    'a': a,
                    'delta': delta,
                    'gamma': gamma
                })
        
        if not valid_configs:
            raise ValueError("No se encontraron configuraciones válidas")
        
        # Encontrar configuración con a mínimo
        best = min(valid_configs, key=lambda x: x['a'])
        
        return {
            'a': best['a'],
            'delta_star': best['delta'],
            'gamma': best['gamma'],
            'method': 'bootstrap',
            'total_valid': len(valid_configs)
        }
    
    def run_all_methods(self):
        """Ejecuta los 3 métodos y valida consistencia"""
        print("🔬 Ejecutando calibración con 3 métodos independientes...\n")
        
        results = {}
        for name, method in self.methods.items():
            print(f"⚙️ Método: {name}")
            try:
                result = method()
                results[name] = result
                print(f"   ✅ a = {result['a']:.2f}, γ = {result['gamma']:.6f}")
            except Exception as e:
                print(f"   ❌ Error: {e}")
                results[name] = None
            print()
        
        # Validar consistencia
        valid_results = [r for r in results.values() if r is not None]
        
        if len(valid_results) < 2:
            raise ValueError("No hay suficientes métodos válidos")
        
        a_values = [r['a'] for r in valid_results]
        a_mean = np.mean(a_values)
        a_std = np.std(a_values)
        
        print(f"📊 RESUMEN DE VALIDACIÓN CRUZADA:")
        print(f"   a promedio: {a_mean:.2f} ± {a_std:.2f}")
        print(f"   Consistencia: {'✅ ALTA' if a_std/a_mean < 0.1 else '⚠️ MEDIA'}")
        
        # Seleccionar valor conservador (más alto para seguridad)
        a_final = max(a_values)
        
        print(f"\n🎯 VALOR FINAL (conservador): a = {a_final:.2f}")
        
        # Guardar resultados
        output = {
            'a_calibrated': a_final,
            'methods': results,
            'statistics': {
                'mean': a_mean,
                'std': a_std,
                'consistency': 'high' if a_std/a_mean < 0.1 else 'medium'
            }
        }
        
        Path('calibration').mkdir(exist_ok=True)
        with open('calibration/optimal_a.json', 'w') as f:
            json.dump(output, f, indent=2)
        
        print(f"\n💾 Resultados guardados en: calibration/optimal_a.json")
        
        return output


if __name__ == "__main__":
    calibrator = CompleteCalibratorValidator()
    results = calibrator.run_all_methods()
    
    print("\n✅ CALIBRACIÓN COMPLETA")
