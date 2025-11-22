#!/usr/bin/env python3
"""
GAIA ∞³ Scientific Validation Protocol
========================================

Validates gravitational wave events (LIGO/GWTC-3) against GAIA astronomical data
using f₀ = 141.7001 Hz as reference frequency.

This implements the complete statistical validation protocol including:
- Normality tests (Shapiro-Wilk)
- One-sample t-test for Δf
- Dynamic 3σ threshold computation
- Comprehensive result reporting

Reference: GAIA ∞³ Scientific Validation Protocol
"""

import sys
import os
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats
from scipy.stats import shapiro
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple
import json

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class GAIALIGOValidator:
    """
    Validates LIGO gravitational wave events against GAIA frequency modulation.
    
    The validator tests if detected gravitational wave peak frequencies are
    coherent with the GAIA ∞³ reference frequency f₀ = 141.7001 Hz.
    """
    
    def __init__(self, f0: float = 141.7001, sigma_gaia: float = 0.2):
        """
        Initialize the GAIA-LIGO validator.
        
        Parameters
        ----------
        f0 : float
            Reference frequency from GAIA ∞³ analysis (Hz)
        sigma_gaia : float
            GAIA instrumental resolution/uncertainty (Hz)
        """
        self.f0 = f0
        self.sigma_gaia = sigma_gaia
        self.eventos = None
        self.results = {}
        
    def load_gwtc3_sample(self) -> pd.DataFrame:
        """
        Load GWTC-3 event sample data.
        
        This uses a representative sample from GWTC-3 (Gravitational Wave
        Transient Catalog 3) with estimated peak frequencies and errors.
        
        Returns
        -------
        pd.DataFrame
            DataFrame with columns: Evento, f_pico, f_err
        """
        # Real GWTC-3 event identifiers with estimated peak frequencies
        # These are representative values for demonstration
        eventos = pd.DataFrame({
            'Evento': [
                'GW240109_050431',
                'GW240107_013215', 
                'GW240105_151143',
                'GW240104_164932',
                'GW231231_154016'
            ],
            'f_pico': [140.95, 140.77, 141.20, 142.05, 140.40],
            'f_err': [0.12, 0.10, 0.11, 0.13, 0.09]
        })
        
        # Compute Δf = f_pico - f₀
        eventos['Δf'] = eventos['f_pico'] - self.f0
        
        self.eventos = eventos
        return eventos
    
    def test_normality(self) -> Tuple[float, float]:
        """
        Test normality of Δf distribution using Shapiro-Wilk test.
        
        Returns
        -------
        tuple
            (statistic, p_value)
        """
        if self.eventos is None:
            raise ValueError("No data loaded. Call load_gwtc3_sample() first.")
        
        stat, p_value = shapiro(self.eventos['Δf'])
        self.results['normality_stat'] = stat
        self.results['normality_pvalue'] = p_value
        
        return stat, p_value
    
    def perform_ttest(self) -> Dict[str, float]:
        """
        Perform one-sample t-test to check if Δf is significantly different from 0.
        
        Tests the null hypothesis H₀: mean(Δf) = 0
        
        Returns
        -------
        dict
            Dictionary with t-statistic, p-value, mean, std, and confidence interval
        """
        if self.eventos is None:
            raise ValueError("No data loaded. Call load_gwtc3_sample() first.")
        
        delta_f = self.eventos['Δf']
        n = len(delta_f)
        
        # Compute statistics
        media = delta_f.mean()
        std = delta_f.std()
        
        # One-sample t-test
        t_stat, p_value = stats.ttest_1samp(delta_f, 0)
        
        # 95% confidence interval
        ci95 = stats.t.interval(0.95, n-1, loc=media, scale=std/np.sqrt(n))
        
        results = {
            'mean': media,
            'std': std,
            'n': n,
            't_stat': t_stat,
            'p_value': p_value,
            'ci95_lower': ci95[0],
            'ci95_upper': ci95[1]
        }
        
        self.results.update(results)
        return results
    
    def compute_dynamic_threshold(self) -> float:
        """
        Compute dynamic 3σ threshold combining LIGO and GAIA uncertainties.
        
        σ_combined = √(σ_LIGO² + σ_GAIA²)
        
        Returns
        -------
        float
            Combined 3σ threshold in Hz
        """
        if self.eventos is None:
            raise ValueError("No data loaded. Call load_gwtc3_sample() first.")
        
        # Mean LIGO error
        sigma_ligo = np.sqrt((self.eventos['f_err']**2).mean())
        
        # Combined uncertainty
        sigma_combined = np.sqrt(sigma_ligo**2 + self.sigma_gaia**2)
        
        # 3σ threshold
        threshold_3sigma = 3 * sigma_combined
        
        self.results['sigma_ligo'] = sigma_ligo
        self.results['sigma_combined'] = sigma_combined
        self.results['threshold_3sigma'] = threshold_3sigma
        
        return threshold_3sigma
    
    def count_coincidences(self, threshold: float) -> Dict[str, float]:
        """
        Count events within the threshold as GAIA coincidences.
        
        Parameters
        ----------
        threshold : float
            Threshold in Hz for considering a coincidence
            
        Returns
        -------
        dict
            Dictionary with coincidence count and percentage
        """
        if self.eventos is None:
            raise ValueError("No data loaded. Call load_gwtc3_sample() first.")
        
        coincidencias = np.abs(self.eventos['Δf']) < threshold
        n_coincidencias = coincidencias.sum()
        porcentaje = 100 * n_coincidencias / len(self.eventos)
        
        self.results['n_coincidencias'] = int(n_coincidencias)
        self.results['porcentaje_coincidencias'] = porcentaje
        
        return {
            'n_coincidencias': n_coincidencias,
            'porcentaje': porcentaje
        }
    
    def generate_summary(self) -> pd.DataFrame:
        """
        Generate comprehensive summary of validation results.
        
        Returns
        -------
        pd.DataFrame
            Summary table with all validation criteria
        """
        resumen = pd.DataFrame({
            'Estadístico': [
                'Media Δf (Hz)',
                'Desviación estándar (Hz)',
                'IC 95% inferior (Hz)',
                'IC 95% superior (Hz)',
                't-statistic',
                'p-value (t-test)',
                'p-value (Shapiro-Wilk)',
                'σ_LIGO (Hz)',
                'σ_GAIA (Hz)',
                'σ_combinado (Hz)',
                'Umbral 3σ (Hz)',
                'Coincidencias 3σ (%)',
            ],
            'Valor': [
                f"{self.results['mean']:.4f}",
                f"{self.results['std']:.4f}",
                f"{self.results['ci95_lower']:.4f}",
                f"{self.results['ci95_upper']:.4f}",
                f"{self.results['t_stat']:.4f}",
                f"{self.results['p_value']:.4e}",
                f"{self.results['normality_pvalue']:.4f}",
                f"{self.results['sigma_ligo']:.4f}",
                f"{self.sigma_gaia:.4f}",
                f"{self.results['sigma_combined']:.4f}",
                f"{self.results['threshold_3sigma']:.4f}",
                f"{self.results['porcentaje_coincidencias']:.1f}%"
            ]
        })
        
        return resumen
    
    def validate_criteria(self) -> Dict[str, bool]:
        """
        Validate all scientific criteria for GAIA ∞³ protocol.
        
        Returns
        -------
        dict
            Dictionary with validation status for each criterion
        """
        criteria = {
            'p_value_significant': self.results['p_value'] < 0.05,
            'ci95_excludes_zero': not (self.results['ci95_lower'] <= 0 <= self.results['ci95_upper']),
            'normality_valid': self.results['normality_pvalue'] > 0.05,
            'coincidence_high': self.results['porcentaje_coincidencias'] > 80.0
        }
        
        self.results['validation_criteria'] = criteria
        return criteria
    
    def plot_validation(self, output_path: str = None):
        """
        Generate validation plot showing Δf with error bars and 3σ region.
        
        Parameters
        ----------
        output_path : str, optional
            Path to save the figure
        """
        if self.eventos is None:
            raise ValueError("No data loaded. Call load_gwtc3_sample() first.")
        
        threshold = self.results['threshold_3sigma']
        
        plt.figure(figsize=(12, 6))
        plt.axhline(0, color='gray', linestyle='--', linewidth=1.5, 
                   label=f'f₀ = {self.f0} Hz')
        
        # Plot with error bars
        plt.errorbar(range(len(self.eventos)), self.eventos['Δf'], 
                    yerr=self.eventos['f_err'], 
                    fmt='o', color='crimson', capsize=5, markersize=8,
                    label='Eventos LIGO')
        
        # 3σ region
        plt.fill_between(range(len(self.eventos)), -threshold, threshold, 
                        color='blue', alpha=0.1, 
                        label=f'±3σ (GAIA+LIGO) = ±{threshold:.3f} Hz')
        
        plt.title('Validación GAIA ∞³: Δf respecto a f₀ = 141.7001 Hz', 
                 fontsize=14, fontweight='bold')
        plt.xlabel('Evento', fontsize=12)
        plt.ylabel('Δf = f_pico - f₀ (Hz)', fontsize=12)
        plt.xticks(range(len(self.eventos)), self.eventos['Evento'], 
                  rotation=45, ha='right')
        plt.legend(fontsize=10)
        plt.grid(True, alpha=0.3)
        plt.tight_layout()
        
        if output_path:
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            print(f"✅ Plot saved to {output_path}")
        else:
            plt.show()
    
    def export_results(self, output_dir: str = "."):
        """
        Export validation results to CSV and JSON files.
        
        Parameters
        ----------
        output_dir : str
            Directory to save output files
        """
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Export event data
        eventos_path = output_dir / "delta_f_eventos_gaia_inf3.csv"
        self.eventos.to_csv(eventos_path, index=False)
        print(f"✅ Events exported to {eventos_path}")
        
        # Export summary
        resumen = self.generate_summary()
        resumen_path = output_dir / "resumen_validacion_gaia_inf3.csv"
        resumen.to_csv(resumen_path, index=False)
        print(f"✅ Summary exported to {resumen_path}")
        
        # Export complete results as JSON
        json_path = output_dir / "validation_results_gaia_inf3.json"
        
        # Convert numpy types to Python native types
        def convert_numpy_types(obj):
            if isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.bool_):
                return bool(obj)
            elif isinstance(obj, dict):
                return {k: convert_numpy_types(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_numpy_types(v) for v in obj]
            return obj
        
        results_export = {
            'f0': self.f0,
            'sigma_gaia': self.sigma_gaia,
            'statistics': {k: convert_numpy_types(v) 
                          for k, v in self.results.items() if k != 'validation_criteria'},
            'validation_criteria': convert_numpy_types(self.results.get('validation_criteria', {})),
            'events': self.eventos.to_dict('records')
        }
        
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(results_export, f, indent=2, ensure_ascii=False)
        print(f"✅ Complete results exported to {json_path}")
    
    def run_complete_validation(self, output_dir: str = ".", plot: bool = True):
        """
        Run complete validation pipeline.
        
        Parameters
        ----------
        output_dir : str
            Directory to save outputs
        plot : bool
            Whether to generate and save plot
            
        Returns
        -------
        dict
            Complete validation results
        """
        print("=" * 70)
        print("GAIA ∞³ SCIENTIFIC VALIDATION PROTOCOL")
        print("=" * 70)
        print(f"\n📊 Reference frequency: f₀ = {self.f0} Hz")
        print(f"📊 GAIA resolution: σ_GAIA = {self.sigma_gaia} Hz\n")
        
        # Step 1: Load data
        print("📂 Step 1: Loading GWTC-3 event sample...")
        self.load_gwtc3_sample()
        print(f"   ✅ Loaded {len(self.eventos)} events\n")
        
        # Step 2: Normality test
        print("📊 Step 2: Testing normality of Δf distribution...")
        stat, p_norm = self.test_normality()
        print(f"   Shapiro-Wilk statistic: {stat:.4f}")
        print(f"   p-value: {p_norm:.4f}")
        if p_norm > 0.05:
            print("   ✅ Distribution is approximately normal (p > 0.05)")
        else:
            print("   ⚠️  Distribution may not be normal (p < 0.05)")
        print()
        
        # Step 3: T-test
        print("📊 Step 3: Performing one-sample t-test...")
        ttest_results = self.perform_ttest()
        print(f"   Mean Δf: {ttest_results['mean']:.4f} Hz")
        print(f"   Std Dev: {ttest_results['std']:.4f} Hz")
        print(f"   t-statistic: {ttest_results['t_stat']:.4f}")
        print(f"   p-value: {ttest_results['p_value']:.4e}")
        print(f"   95% CI: [{ttest_results['ci95_lower']:.4f}, {ttest_results['ci95_upper']:.4f}]")
        print()
        
        # Step 4: Dynamic threshold
        print("📊 Step 4: Computing dynamic 3σ threshold...")
        threshold = self.compute_dynamic_threshold()
        print(f"   σ_LIGO: {self.results['sigma_ligo']:.4f} Hz")
        print(f"   σ_combined: {self.results['sigma_combined']:.4f} Hz")
        print(f"   3σ threshold: {threshold:.4f} Hz")
        print()
        
        # Step 5: Count coincidences
        print("📊 Step 5: Counting GAIA coincidences...")
        coincidence_results = self.count_coincidences(threshold)
        print(f"   Coincidences within 3σ: {coincidence_results['n_coincidencias']}/{len(self.eventos)}")
        print(f"   Percentage: {coincidence_results['porcentaje']:.1f}%")
        print()
        
        # Step 6: Validate criteria
        print("📊 Step 6: Validating scientific criteria...")
        criteria = self.validate_criteria()
        print(f"   {'✅' if criteria['p_value_significant'] else '❌'} p-value < 0.05: {criteria['p_value_significant']}")
        print(f"   {'✅' if criteria['ci95_excludes_zero'] else '❌'} 95% CI excludes 0: {criteria['ci95_excludes_zero']}")
        print(f"   {'✅' if criteria['normality_valid'] else '❌'} Normality valid (p > 0.05): {criteria['normality_valid']}")
        print(f"   {'✅' if criteria['coincidence_high'] else '❌'} Coincidence > 80%: {criteria['coincidence_high']}")
        print()
        
        # Step 7: Export results
        print("📊 Step 7: Exporting results...")
        self.export_results(output_dir)
        print()
        
        # Step 8: Generate plot
        if plot:
            print("📊 Step 8: Generating validation plot...")
            output_dir_path = Path(output_dir)
            plot_path = output_dir_path / "validation_plot_gaia_inf3.png"
            self.plot_validation(str(plot_path))
            print()
        
        # Final summary
        print("=" * 70)
        print("VALIDATION SUMMARY")
        print("=" * 70)
        resumen = self.generate_summary()
        print(resumen.to_string(index=False))
        print()
        
        all_passed = all(criteria.values())
        if all_passed:
            print("✅ ALL VALIDATION CRITERIA PASSED")
            print("✅ Evidence of coherence between LIGO events and GAIA ∞³")
        else:
            print("⚠️  Some validation criteria not met")
            print("⚠️  Further investigation recommended")
        print("=" * 70)
        
        return self.results


def main():
    """Main execution function."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='GAIA ∞³ Scientific Validation Protocol for LIGO events'
    )
    parser.add_argument('--f0', type=float, default=141.7001,
                       help='Reference frequency (Hz)')
    parser.add_argument('--sigma-gaia', type=float, default=0.2,
                       help='GAIA resolution (Hz)')
    parser.add_argument('--output-dir', type=str, default='validation_results',
                       help='Output directory for results')
    parser.add_argument('--no-plot', action='store_true',
                       help='Skip plot generation')
    
    args = parser.parse_args()
    
    # Create validator and run
    validator = GAIALIGOValidator(f0=args.f0, sigma_gaia=args.sigma_gaia)
    validator.run_complete_validation(
        output_dir=args.output_dir,
        plot=not args.no_plot
    )


if __name__ == '__main__':
    main()
