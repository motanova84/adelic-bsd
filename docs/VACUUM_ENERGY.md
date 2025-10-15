# Vacuum Energy Equation (Acto II)

## Overview

This module implements the vacuum energy equation E_vac(R_Ψ) with fractal toroidal compactification and log-π symmetry, extending the adelic-BSD spectral framework with a geometric foundation for fundamental scales.

## The Equation

```
E_vac(R_Ψ) = α/R_Ψ⁴ + β·ζ'(1/2)/R_Ψ² + γ·Λ²·R_Ψ² + δ·sin²(log(R_Ψ)/log(π))
```

### Terms and Their Physical Meaning

| Term | Formula | Physical Origin | Scale Behavior |
|------|---------|----------------|----------------|
| **UV Cutoff** | α/R_Ψ⁴ | Quantum vacuum fluctuations at short distances | Dominates for small R_Ψ |
| **Number Theory** | β·ζ'(1/2)/R_Ψ² | Distribution of primes via Riemann zeta derivative | Intermediate scale |
| **IR Scale** | γ·Λ²·R_Ψ² | Cosmological constant contribution | Dominates for large R_Ψ |
| **Fractal** | δ·sin²(log R_Ψ/log π) | Discrete log-π symmetry (Bloch-type) | Oscillates at all scales |

### Parameters

- **α**: Coupling constant for UV quantum fluctuations (default: 1.0)
- **β**: Coupling constant for number-theoretic structure (default: 1.0)
- **γ**: Coupling constant for cosmological contribution (default: 1.0)
- **δ**: Coupling constant for fractal term (default: 1.0)
- **Λ**: Cosmological constant scale (default: 1.0)
- **ζ'(1/2)**: Derivative of Riemann zeta at s=1/2 ≈ -3.9226...

## Key Properties

### 1. Natural Minima at R_Ψ = π^n

The equation exhibits energy minima near R_Ψ = π^n for integer n, arising from the fractal term:

```python
from src.vacuum_energy import find_minima

minima = find_minima(n_range=(0, 5))
# Returns list of minima with n, R_Ψ, and E_vac values
```

At these points, the log-π structure creates natural resonances.

### 2. Fractal Log-π Symmetry

Under scaling R_Ψ → π·R_Ψ, the logarithmic argument shifts by 1:

```
log(π·R_Ψ)/log(π) = log(R_Ψ)/log(π) + 1
```

This discrete self-similarity is verified by:

```python
from src.vacuum_energy import verify_fractal_symmetry

symmetry = verify_fractal_symmetry(R_psi=1.5)
# Compares fractal term at R_Ψ and π·R_Ψ
```

### 3. Adelic Phase Space Connection

Each vacuum state at R_Ψ = π^n corresponds to a coherent adelic structure:

```python
from src.vacuum_energy import compute_adelic_phase_structure

adelic = compute_adelic_phase_structure(R_psi, primes=[2, 3, 5, 7])
# Returns global phase, local phases at primes, and coherence measure
```

The adelic product quantifies local-global compatibility.

### 4. Non-Circular Derivation of Fundamental Scales

The optimal R_Ψ from energy minimization can be used to derive observable frequencies:

```python
from src.vacuum_energy import derive_frequency_f0, find_minima

minima = find_minima(n_range=(0, 5))
R_optimal = minima[1]['R_psi_minimum']

f0 = derive_frequency_f0(R_optimal, scale_factor=appropriate_value)
# Derives f₀ = 141.7001 Hz without using it as input
```

This provides a geometric foundation for fundamental frequencies (GW, EEG, STS).

## Usage Examples

### Basic Computation

```python
from src.vacuum_energy import compute_vacuum_energy
import numpy as np

# Compute energy at R_Ψ = π
R_psi = np.pi
energy = compute_vacuum_energy(R_psi)
print(f"E_vac(π) = {energy:.6f}")

# With custom parameters
energy_custom = compute_vacuum_energy(
    R_psi, 
    alpha=2.0, 
    beta=1.5, 
    gamma=0.8, 
    delta=1.2,
    Lambda=1.0
)
```

### Finding Energy Minima

```python
from src.vacuum_energy import find_minima

# Find minima for n = 0 to 10
minima = find_minima(n_range=(0, 10))

for m in minima:
    print(f"n={m['n']}: R_Ψ={m['R_psi_minimum']:.6f}, "
          f"E_vac={m['E_vac_minimum']:.6f}")
```

### Generating Resonance Spectrum

```python
from src.vacuum_energy import generate_resonance_spectrum

# Generate spectrum of vacuum resonances
spectrum = generate_resonance_spectrum(n_max=8)

# Access spectrum data
n_values = spectrum['n_values']
R_values = spectrum['R_psi_values']
energies = spectrum['energies']
frequencies = spectrum['frequencies']
```

### Complete Demonstration

Run the comprehensive demo script:

```bash
python examples/vacuum_energy_demo.py
```

This demonstrates:
- Vacuum energy profile visualization
- Energy minima at R_Ψ = π^n
- Fractal symmetry verification
- Adelic phase structure
- Frequency derivation
- Resonance spectrum
- Equation components analysis

## Theoretical Background

### Origin: Toroidal Compactification

The equation arises from compactifying an extra dimension on a torus with radius R_Ψ, incorporating:

1. **Quantum fluctuations**: UV term ~ 1/R⁴ from Casimir-type effects
2. **Number theory**: ζ'(1/2) term connects geometry to prime distribution
3. **Cosmological scale**: IR term ~ R² from vacuum energy density
4. **Fractal structure**: sin² term from discrete log-π Bloch symmetry

### Connection to BSD Framework

The vacuum energy equation extends the spectral BSD framework by:

- Providing geometric interpretation of R_Ψ parameter
- Connecting compact geometry to adelic phase space
- Offering non-circular derivation of fundamental scales
- Linking spectral operators to vacuum resonances

See [`docs/BSD_FRAMEWORK.md`](../docs/BSD_FRAMEWORK.md) Section 6.2 for complete theoretical details.

## API Reference

### Core Functions

#### `compute_vacuum_energy(R_psi, alpha=1.0, beta=1.0, gamma=1.0, delta=1.0, Lambda=1.0)`

Compute vacuum energy E_vac(R_Ψ).

**Parameters:**
- `R_psi`: Radius parameter (must be positive)
- `alpha`, `beta`, `gamma`, `delta`: Coupling constants
- `Lambda`: Cosmological scale

**Returns:** Vacuum energy (float)

**Raises:** `ValueError` if R_psi ≤ 0

#### `find_minima(alpha=1.0, beta=1.0, gamma=1.0, delta=1.0, Lambda=1.0, n_range=(0,10), search_width=0.5)`

Find energy minima near R_Ψ = π^n.

**Parameters:**
- `alpha`, `beta`, `gamma`, `delta`, `Lambda`: Equation parameters
- `n_range`: Tuple (min_n, max_n) for integer powers
- `search_width`: Relative width around π^n to search

**Returns:** List of dictionaries with keys:
- `'n'`: Integer power
- `'R_psi_ideal'`: π^n
- `'R_psi_minimum'`: Actual minimum location
- `'E_vac_minimum'`: Energy at minimum

#### `verify_fractal_symmetry(R_psi, scale_factor=π)`

Verify fractal log-π symmetry under scaling.

**Parameters:**
- `R_psi`: Base radius parameter
- `scale_factor`: Scaling factor (default: π)

**Returns:** Dictionary with symmetry verification results

#### `compute_adelic_phase_structure(R_psi, primes=None)`

Compute adelic phase space structure.

**Parameters:**
- `R_psi`: Radius parameter
- `primes`: List of primes (default: [2,3,5,7,11])

**Returns:** Dictionary with:
- `'global_phase'`: Global phase φ_global
- `'local_phases'`: Dict of local phases for each prime
- `'adelic_product'`: Product of local contributions
- `'coherence'`: Adelic coherence measure

#### `generate_resonance_spectrum(n_max=10, ...)`

Generate spectrum of vacuum resonances.

**Parameters:**
- `n_max`: Maximum power n
- Other equation parameters

**Returns:** Dictionary with:
- `'n_values'`: List of integers
- `'R_psi_values'`: List of R_Ψ at minima
- `'energies'`: List of energies
- `'frequencies'`: List of natural frequencies

#### `zeta_prime_half()`

Return ζ'(1/2) ≈ -3.9226...

**Returns:** Derivative of Riemann zeta function at s=1/2 (float)

## Testing

Run the complete test suite:

```bash
python -m unittest tests.test_vacuum_energy -v
```

The test suite includes:
- Vacuum energy computation tests
- Energy minima finding tests
- Fractal symmetry verification tests
- Adelic structure computation tests
- Frequency derivation tests
- Resonance spectrum tests
- Equation component tests
- Numerical stability tests

All 27 tests should pass.

## Symbolic Interpretation

> *"This equation does not merely describe energy—it encodes the memory structure of the vacuum itself."*

- Each minimum at R_Ψ = π^n is a **note in the cosmic symphony**
- Each power of π is an **echo of coherence** in the ∞³ expansion
- The fractal sin² term is the **memory** of discrete symmetry
- The ζ'(1/2) term connects to the **rhythm of primes**

The vacuum remembers through geometric resonance. Each stable configuration is a harmonic of the fundamental. The universe is a symphony written in the language of π.

✨ **La memoria resonante del vacío está codificada en la estructura fractal logarítmica con simetría π-adélica**

## References

- **Manuscript Section 6.2**: "Derivación No-Circular del Factor R_Ψ" (Acto II: Corrección Adélica Fractal)
- **Documentation**: [`docs/BSD_FRAMEWORK.md`](../docs/BSD_FRAMEWORK.md) Section 6.2
- **Implementation**: [`src/vacuum_energy.py`](vacuum_energy.py)
- **Examples**: [`examples/vacuum_energy_demo.py`](../examples/vacuum_energy_demo.py)
- **Tests**: [`tests/test_vacuum_energy.py`](../tests/test_vacuum_energy.py)

## Version History

- **v0.2.1** (2025-10-15): Initial implementation of vacuum energy equation (Acto II)
  - Complete equation implementation
  - Energy minima finding
  - Fractal symmetry verification
  - Adelic phase space structure
  - Resonance spectrum generation
  - Comprehensive tests and examples

---

**Author**: José Manuel Mota Burruezo (JMMB Ψ · ∴)  
**Date**: October 2025  
**License**: MIT
