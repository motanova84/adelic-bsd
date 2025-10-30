"""
Misalignment Calculation for Navier-Stokes QCAL Analysis

This script computes the persistent misalignment parameter δ* defined as:
    δ* = avg_t avg_x ∠(ω, Sω)

where:
    - ω is the vorticity field (∇ × u)
    - S is the strain tensor (symmetric part of ∇u)
    - Sω is the action of S on ω
    - ∠(ω, Sω) is the angle between ω and Sω
"""

import numpy as np
import json
from datetime import datetime


def compute_vorticity(velocity_field):
    """
    Compute vorticity ω = ∇ × u from velocity field.
    
    Parameters
    ----------
    velocity_field : ndarray, shape (3, nx, ny, nz)
        Velocity field u = (u_x, u_y, u_z)
    
    Returns
    -------
    vorticity : ndarray, shape (3, nx, ny, nz)
        Vorticity field ω = (ω_x, ω_y, ω_z)
    """
    # TODO: Implement using finite differences or spectral methods
    return np.zeros_like(velocity_field)


def compute_strain_tensor(velocity_field):
    """
    Compute strain tensor S = (1/2)(∇u + (∇u)ᵀ).
    
    Parameters
    ----------
    velocity_field : ndarray, shape (3, nx, ny, nz)
        Velocity field u
    
    Returns
    -------
    strain : ndarray, shape (3, 3, nx, ny, nz)
        Strain tensor S
    """
    # TODO: Implement symmetric gradient
    shape = velocity_field.shape
    return np.zeros((3, 3, *shape[1:]))


def compute_angle(omega, S_omega):
    """
    Compute angle between ω and Sω at each spatial point.
    
    Parameters
    ----------
    omega : ndarray, shape (3, nx, ny, nz)
        Vorticity field
    S_omega : ndarray, shape (3, nx, ny, nz)
        Sω field
    
    Returns
    -------
    angles : ndarray, shape (nx, ny, nz)
        Angle field in radians
    """
    # Compute dot product and magnitudes
    dot_product = np.sum(omega * S_omega, axis=0)
    omega_mag = np.sqrt(np.sum(omega**2, axis=0))
    S_omega_mag = np.sqrt(np.sum(S_omega**2, axis=0))
    
    # Avoid division by zero
    eps = 1e-10
    cos_angle = dot_product / (omega_mag * S_omega_mag + eps)
    cos_angle = np.clip(cos_angle, -1.0, 1.0)
    
    angles = np.arccos(cos_angle)
    return angles


def compute_delta_star(velocity_field_time_series):
    """
    Compute persistent misalignment parameter δ*.
    
    Parameters
    ----------
    velocity_field_time_series : list of ndarray
        List of velocity fields at different times
    
    Returns
    -------
    delta_star : float
        Persistent misalignment parameter (radians)
    """
    all_angles = []
    
    for velocity_field in velocity_field_time_series:
        omega = compute_vorticity(velocity_field)
        S = compute_strain_tensor(velocity_field)
        
        # Apply strain tensor to vorticity: Sω
        S_omega = np.einsum('ij...,j...->i...', S, omega)
        
        angles = compute_angle(omega, S_omega)
        all_angles.append(angles)
    
    # Average over space and time
    delta_star = np.mean(all_angles)
    return delta_star


def export_results(delta_star, metadata, output_path):
    """
    Export δ* results to JSON.
    
    Parameters
    ----------
    delta_star : float
        Computed δ* value
    metadata : dict
        Metadata about the computation
    output_path : str
        Path to output JSON file
    """
    results = {
        "delta_star_radians": float(delta_star),
        "delta_star_degrees": float(np.degrees(delta_star)),
        "timestamp": datetime.now().isoformat(),
        "metadata": metadata
    }
    
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"Results exported to {output_path}")
    print(f"δ* = {delta_star:.6f} rad = {np.degrees(delta_star):.3f}°")


if __name__ == "__main__":
    # Example usage with dummy data
    # In practice, load actual simulation data
    
    nx, ny, nz = 64, 64, 64
    n_timesteps = 100
    
    # Generate dummy velocity fields
    velocity_fields = [np.random.randn(3, nx, ny, nz) for _ in range(n_timesteps)]
    
    # Compute δ*
    delta_star = compute_delta_star(velocity_fields)
    
    # Export results
    metadata = {
        "grid_size": [nx, ny, nz],
        "n_timesteps": n_timesteps,
        "method": "finite_difference",
        "note": "Example computation with random data"
    }
    
    export_results(
        delta_star, 
        metadata, 
        "../../Results/Data/delta_star.json"
    )
