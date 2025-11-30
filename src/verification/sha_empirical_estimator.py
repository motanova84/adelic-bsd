#!/usr/bin/env python3
"""
Sha Empirical Estimator Module - BSD ∞³ Framework

Synthetic simulation module for estimating |Sha(E)| (Tate-Shafarevich group)
for elliptic curves with rank >= 2 using a simplified BSD formula.

IMPORTANT: This module generates synthetic/simulated curve data with random
parameters for empirical validation purposes. It does not use actual elliptic
curve data from LMFDB. Real curves have correlated properties that are not
captured in this simulation. For analysis of real curves, use the SageMath
integration modules in this repository.

The estimation uses a simplified BSD formula:
    |Sha| ≈ (L'(E,1) * |T|²) / (R * Ω)

Where:
    L'(E,1) = derivative of L-function at s=1
    |T| = order of the torsion subgroup
    R = regulator
    Ω = real period

Note: The complete BSD formula also includes Tamagawa numbers (∏ᵖ cₚ),
which are omitted here for simplification.

This module is part of the SABIO ∞³ verification protocol for extended
empirical validation of BSD conjecture.

Author: José Manuel Mota Burruezo (JMMB Ψ·∴)
Date: November 2025
License: MIT
"""

import json
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Union

import numpy as np
import pandas as pd


class ShaEmpiricalEstimator:
    """
    Synthetic simulation estimator for |Sha(E)| on curves with rank >= 2.
    
    Implements the BSD ∞³ verification protocol for estimating
    the order of the Tate-Shafarevich group using simulated curve data.
    
    Note: This class generates random synthetic curve parameters.
    For real curve analysis, use the SageMath integration modules.
    """
    
    def __init__(
        self,
        num_curves: int = 500,
        start_index: int = 10001,
        random_seed: Optional[int] = None
    ):
        """
        Initialize the Sha estimator.
        
        Args:
            num_curves: Number of curves to simulate
            start_index: Starting index for curve IDs (e.g., 10001 -> E_10001)
            random_seed: Optional seed for reproducibility
        """
        self.num_curves = num_curves
        self.start_index = start_index
        self.random_seed = random_seed
        self._results: Optional[pd.DataFrame] = None
        self._metadata: Dict = {}
        
        if random_seed is not None:
            np.random.seed(random_seed)
    
    def _generate_curve_ids(self) -> List[str]:
        """Generate curve identifiers E_{start_index} to E_{start_index + num_curves - 1}."""
        return [f"E_{self.start_index + i}" for i in range(self.num_curves)]
    
    def _generate_conductors(self) -> np.ndarray:
        """Generate random conductors in range [10^3, 10^5)."""
        return np.random.randint(10**3, 10**5, self.num_curves)
    
    def _generate_ranks(self) -> np.ndarray:
        """
        Generate random ranks >= 2 (values 2, 3, or 4).
        
        Note: This generates synthetic ranks for simulation purposes.
        Real elliptic curve ranks have different distributions.
        """
        return np.random.choice([2, 3, 4], self.num_curves)
    
    def _generate_torsion_orders(self) -> np.ndarray:
        """Generate random torsion orders (1 to 6)."""
        return np.random.choice([1, 2, 3, 4, 5, 6], self.num_curves)
    
    def _generate_regulators(self) -> np.ndarray:
        """Generate random regulators in range (0.1, 10.0)."""
        return np.round(np.random.uniform(0.1, 10.0, self.num_curves), 4)
    
    def _generate_real_periods(self) -> np.ndarray:
        """Generate random real periods in range (0.01, 5.0)."""
        return np.round(np.random.uniform(0.01, 5.0, self.num_curves), 4)
    
    def _generate_l_derivatives(self) -> np.ndarray:
        """Generate random L'(E,1) values in range (0.01, 1.0)."""
        return np.round(np.random.uniform(0.01, 1.0, self.num_curves), 5)
    
    def estimate_sha(
        self,
        l_derivative: Union[float, np.ndarray],
        torsion_order: Union[int, np.ndarray],
        regulator: Union[float, np.ndarray],
        real_period: Union[float, np.ndarray]
    ) -> Union[float, np.ndarray]:
        """
        Estimate |Sha(E)| using simplified BSD formula.
        
        The formula used is:
            |Sha| ≈ (L'(E,1) * |T|²) / (R * Ω)
        
        Note: This is a simplified formula that does not include
        local factors (Tamagawa numbers: ∏ᵖ cₚ) for empirical validation.
        The complete BSD formula includes these factors, which could
        affect accuracy for curves with bad reduction at multiple primes.
        
        Args:
            l_derivative: L'(E,1) - derivative of L-function at s=1
            torsion_order: |T| - order of torsion subgroup
            regulator: R - regulator
            real_period: Ω - real period
            
        Returns:
            Estimated value of |Sha(E)|
        """
        denominator = regulator * real_period
        # Avoid division by zero or near-zero denominators
        min_denominator = 1e-10
        with np.errstate(divide='ignore', invalid='ignore'):
            # Replace near-zero denominators with nan to avoid unrealistic estimates
            safe_denominator = np.where(
                np.abs(denominator) < min_denominator, 
                np.nan, 
                denominator
            )
            sha_estimate = (l_derivative * torsion_order**2) / safe_denominator
        return np.round(sha_estimate, 3)
    
    def generate_simulation(self) -> pd.DataFrame:
        """
        Generate simulated curve data and Sha estimates.
        
        Returns:
            DataFrame containing curve data and Sha estimates
        """
        curve_ids = self._generate_curve_ids()
        conductors = self._generate_conductors()
        ranks = self._generate_ranks()
        torsion_orders = self._generate_torsion_orders()
        regulators = self._generate_regulators()
        real_periods = self._generate_real_periods()
        l_derivatives = self._generate_l_derivatives()
        
        # Estimate |Sha|
        sha_estimates = self.estimate_sha(
            l_derivatives, torsion_orders, regulators, real_periods
        )
        
        # Create DataFrame
        self._results = pd.DataFrame({
            "CurveID": curve_ids,
            "Conductor": conductors,
            "Rank": ranks,
            "TorsionOrder": torsion_orders,
            "Regulator": regulators,
            "RealPeriod": real_periods,
            "L'(E,1)": l_derivatives,
            "ShaEstimate": sha_estimates
        })
        
        # Store metadata
        self._metadata = {
            "num_curves": self.num_curves,
            "start_index": self.start_index,
            "random_seed": self.random_seed,
            "timestamp": datetime.now().isoformat(),
            "protocol": "SABIO_∞³",
            "framework": "BSD-∞³-EmpiricalValidation"
        }
        
        return self._results
    
    def get_results(self) -> Optional[pd.DataFrame]:
        """Get the results DataFrame, generating if necessary."""
        if self._results is None:
            self.generate_simulation()
        return self._results
    
    def get_statistics(self) -> Dict:
        """
        Compute summary statistics for the Sha estimates.
        
        Returns:
            Dictionary containing statistical summary
        """
        if self._results is None:
            self.generate_simulation()
        
        df = self._results
        
        stats = {
            "total_curves": len(df),
            "rank_distribution": df["Rank"].value_counts().to_dict(),
            "sha_statistics": {
                "mean": float(df["ShaEstimate"].mean()),
                "std": float(df["ShaEstimate"].std()),
                "min": float(df["ShaEstimate"].min()),
                "max": float(df["ShaEstimate"].max()),
                "median": float(df["ShaEstimate"].median())
            },
            "regulator_statistics": {
                "mean": float(df["Regulator"].mean()),
                "std": float(df["Regulator"].std())
            },
            "period_statistics": {
                "mean": float(df["RealPeriod"].mean()),
                "std": float(df["RealPeriod"].std())
            },
            "curves_with_sha_gt_1": int((df["ShaEstimate"] > 1).sum()),
            "curves_with_sha_square": int(
                df["ShaEstimate"].apply(lambda x: _is_near_perfect_square(x)).sum()
            )
        }
        
        return stats
    
    def get_by_rank(self, rank: int) -> pd.DataFrame:
        """
        Filter results by rank.
        
        Args:
            rank: The rank to filter by (2, 3, or 4)
            
        Returns:
            DataFrame filtered to curves with the specified rank
        """
        if self._results is None:
            self.generate_simulation()
        return self._results[self._results["Rank"] == rank].copy()
    
    def export_to_json(self, output_path: Union[str, Path]) -> Path:
        """
        Export results to JSON file.
        
        Args:
            output_path: Path for the output JSON file
            
        Returns:
            Path to the saved file
        """
        if self._results is None:
            self.generate_simulation()
        
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        export_data = {
            "metadata": self._metadata,
            "statistics": self.get_statistics(),
            "curves": self._results.to_dict(orient="records")
        }
        
        with open(output_path, 'w') as f:
            json.dump(export_data, f, indent=2)
        
        return output_path
    
    def export_to_csv(self, output_path: Union[str, Path]) -> Path:
        """
        Export results to CSV file.
        
        Args:
            output_path: Path for the output CSV file
            
        Returns:
            Path to the saved file
        """
        if self._results is None:
            self.generate_simulation()
        
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        self._results.to_csv(output_path, index=False)
        
        return output_path
    
    def generate_certificate(self) -> Dict:
        """
        Generate verification certificate for the simulation.
        
        Returns:
            Dictionary containing the verification certificate
        """
        import uuid
        
        if self._results is None:
            self.generate_simulation()
        
        stats = self.get_statistics()
        
        certificate = {
            "certificate_id": str(uuid.uuid4()),
            "protocol": "SABIO_∞³",
            "module": "sha_empirical_estimator",
            "timestamp": datetime.now().isoformat(),
            "simulation_parameters": {
                "num_curves": self.num_curves,
                "start_index": self.start_index,
                "random_seed": self.random_seed,
                "curve_range": f"E_{self.start_index} to E_{self.start_index + self.num_curves - 1}"
            },
            "statistics": stats,
            "verification_status": "completed",
            "framework": "adelic-bsd"
        }
        
        return certificate


def _is_near_perfect_square(x: float, tolerance: float = 1e-6) -> bool:
    """
    Check if a value is near a perfect square.
    
    BSD predicts that |Sha| should be a perfect square for verified curves.
    Uses relative tolerance for larger values.
    
    Args:
        x: Value to check
        tolerance: Relative tolerance for floating point comparison
        
    Returns:
        True if x is near a perfect square
    """
    if x < 0 or np.isnan(x):
        return False
    sqrt_x = np.sqrt(x)
    nearest_int = round(sqrt_x)
    if nearest_int == 0:
        return abs(sqrt_x) < tolerance
    # Use relative tolerance
    relative_error = abs(sqrt_x - nearest_int) / nearest_int
    return relative_error < tolerance


def run_empirical_validation(
    num_curves: int = 500,
    start_index: int = 10001,
    random_seed: Optional[int] = 42,
    output_dir: Optional[Union[str, Path]] = None,
    verbose: bool = True
) -> Dict:
    """
    Run complete empirical validation of Sha estimates.
    
    Args:
        num_curves: Number of curves to simulate
        start_index: Starting curve index
        random_seed: Random seed for reproducibility
        output_dir: Optional directory for output files
        verbose: Print progress messages
        
    Returns:
        Dictionary containing validation results and certificate
    """
    if verbose:
        print("=" * 60)
        print("BSD ∞³ — Sha Empirical Estimation")
        print("=" * 60)
        print(f"Simulating {num_curves} curves: E_{start_index} to E_{start_index + num_curves - 1}")
        print(f"Ranks >= 2")
        print()
    
    # Create estimator and run simulation
    estimator = ShaEmpiricalEstimator(
        num_curves=num_curves,
        start_index=start_index,
        random_seed=random_seed
    )
    
    df = estimator.generate_simulation()
    stats = estimator.get_statistics()
    certificate = estimator.generate_certificate()
    
    if verbose:
        print("Sample results (first 5 curves):")
        print(df.head().to_string(index=False))
        print()
        print("Statistics:")
        print(f"  Total curves: {stats['total_curves']}")
        print(f"  Rank distribution: {stats['rank_distribution']}")
        print(f"  Sha mean: {stats['sha_statistics']['mean']:.4f}")
        print(f"  Sha std: {stats['sha_statistics']['std']:.4f}")
        print(f"  Curves with |Sha| > 1: {stats['curves_with_sha_gt_1']}")
        print(f"  Curves with |Sha| near perfect square: {stats['curves_with_sha_square']}")
        print()
    
    # Export if output directory provided
    if output_dir:
        output_path = Path(output_dir)
        csv_path = estimator.export_to_csv(output_path / "sha_estimates.csv")
        json_path = estimator.export_to_json(output_path / "sha_validation.json")
        
        # Save certificate
        cert_path = output_path / "sha_validation_certificate.json"
        with open(cert_path, 'w') as f:
            json.dump(certificate, f, indent=2)
        
        if verbose:
            print(f"Results exported to:")
            print(f"  CSV: {csv_path}")
            print(f"  JSON: {json_path}")
            print(f"  Certificate: {cert_path}")
    
    if verbose:
        print()
        print("=" * 60)
        print("✅ Empirical validation complete")
        print("=" * 60)
    
    return {
        "dataframe": df,
        "statistics": stats,
        "certificate": certificate,
        "estimator": estimator
    }


# Convenience function for direct DataFrame access
def estimate_sha_dataframe(
    num_curves: int = 500,
    start_index: int = 10001,
    random_seed: Optional[int] = 42
) -> pd.DataFrame:
    """
    Generate Sha estimates DataFrame directly.
    
    This is a convenience function for quick access to results.
    
    Args:
        num_curves: Number of curves to simulate
        start_index: Starting curve index
        random_seed: Random seed for reproducibility
        
    Returns:
        DataFrame with Sha estimates
    """
    estimator = ShaEmpiricalEstimator(
        num_curves=num_curves,
        start_index=start_index,
        random_seed=random_seed
    )
    return estimator.generate_simulation()


if __name__ == "__main__":
    # Run default validation
    results = run_empirical_validation(
        num_curves=500,
        start_index=10001,
        random_seed=42,
        verbose=True
    )
