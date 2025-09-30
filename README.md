# Algoritmo Espectral - Mota Burruezo Framework

A complete implementation of the spectral approach to proving finiteness of the Tate–Shafarevich group Ш(E/ℚ) for elliptic curves over ℚ.

## 📋 Overview

This repository implements a spectral approach to proving the finiteness of the Tate–Shafarevich group Ш(E/ℚ) for elliptic curves. The framework is based on adèlic-spectral methods and provides:

- **Spectral finiteness proofs** for elliptic curves
- **Effective bounds** on the order of Ш(E/ℚ)
- **Certificate generation** in text, LaTeX, and JSON formats
- **Batch processing** for multiple curves
- **Local spectral data** computation for primes of bad reduction

## 🏗️ Architecture

The implementation is modularized into focused components:

### Core Modules

```
src/
├── spectral_finiteness.py      # Main orchestration and API
├── spectral_operator.py        # Spectral operator construction M_E,p(s)
├── kernel_computation.py       # Kernel dimension and lattice analysis
├── global_bound.py             # Global bound computation on #Ш
└── certificate_generator.py    # Certificate generation (text/LaTeX/JSON)
```

### Module Responsibilities

#### `spectral_operator.py`
Constructs spectral operators M_E,p(s) based on local representation theory:
- **Good reduction**: Trivial 1×1 operator
- **Multiplicative reduction**: 2×2 Steinberg operator
- **Supercuspidal reduction**: f_p × f_p operator (f_p = conductor exponent)

**Key function**: `construct_spectral_operator(E, p, s=1)`

#### `kernel_computation.py`
Computes kernel dimensions and analyzes the spectral Selmer lattice:
- Kernel dimension: `dim ker(M_E,p(1))`
- Discreteness verification: `∑_p dim ker(M_E,p(1)) < ∞`
- Lattice structure analysis

**Key functions**: `compute_kernel_dimension(operator)`, `compute_kernel_basis(operator)`

#### `global_bound.py`
Computes effective bounds on #Ш(E/ℚ):
- Local bounds: `b_p = p^(f_p)` at each bad prime
- Global bound: `B = ∏_p b_p`
- Verification against known data when available

**Key function**: `compute_global_bound(E)`

#### `certificate_generator.py`
Generates formal certificates attesting to finiteness:
- Text format: Human-readable
- LaTeX format: Publication-ready
- JSON format: Machine-readable structured data

**Key function**: `generate_certificate(E, proof_data, format='text')`

## 📚 Features

### Spectral Finiteness Prover

The core `SpectralFinitenessProver` class provides:

- **`prove_finiteness()`**: Main method that proves finiteness and computes bounds
- **`construct_spectral_operator(p, s=1)`**: Build M_E,p(s) for prime p
- **`compute_kernel_dimension(operator)`**: Compute dim ker(M_E,p(1))
- **`compute_global_bound()`**: Compute effective bound B on #Ш
- **`compute_spectral_determinant(s=1)`**: Compute det(I - M_E(s)) for BSD identity
- **`compute_c1()`**: Compute correction factor in spectral BSD identity
- **`generate_certificate(format='text')`**: Generate human-readable certificates

### Spectral BSD Identity

The implementation includes verification of the core spectral identity:

```
det(I - M_E(s)) = c(s) · L(E,s)
```

At s=1, this connects the spectral determinant to the L-function value, providing a computational check of the theoretical framework.

### Batch Processing

Process multiple curves efficiently:

```python
from src.spectral_finiteness import batch_prove_finiteness

curves = ['11a1', '11a2', '14a1', '15a1', '17a1']
results = batch_prove_finiteness(curves)

for label, result in results.items():
    if 'error' not in result:
        print(f"{label}: bound = {result['global_bound']}")
```

### Certificate Generation

Generate certificates in multiple formats:

```python
# Text certificate
cert_text = prover.generate_certificate('text')
print(cert_text)

# LaTeX certificate (publication-ready)
cert_latex = prover.generate_certificate('latex')

# JSON certificate (machine-readable)
cert_json = prover.generate_certificate('json')
```

## 🚀 Quick Start

### Installation

```bash
# Clone the repository
git clone https://github.com/motanova84/algoritmo.git
cd algoritmo

# Install dependencies (requires SageMath)
pip install -r requirements.txt
```

### Basic Usage

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

# Create a curve
E = EllipticCurve('11a1')  # y² + y = x³ - x² - 10x - 20

# Create prover
prover = SpectralFinitenessProver(E)

# Prove finiteness
result = prover.prove_finiteness()

# Display results
print(f"Curve: {result['curve_label']}")
print(f"Conductor: {result['spectral_data']['conductor']}")
print(f"Rank: {result['spectral_data']['rank']}")
print(f"Global bound on #Ш: {result['global_bound']}")
print(f"Finiteness proved: {result['finiteness_proved']}")
```

## 📊 Examples

### Example 1: Single Curve Analysis

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('37a1')  # y² + y = x³ - x
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

# Display results
print(f"Curve: {result['curve_label']}")
print(f"Conductor: {result['spectral_data']['conductor']}")
print(f"Rank: {result['spectral_data']['rank']}")
print(f"Global bound on #Ш: {result['global_bound']}")
```

### Example 2: Examining Spectral Operators

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)

# Construct operator at prime 11
M_11 = prover.construct_spectral_operator(11, s=1)
print(f"Spectral operator M_{{E,11}}(1):")
print(M_11)

# Compute kernel dimension
kernel_dim = prover.compute_kernel_dimension(M_11)
print(f"Kernel dimension: {kernel_dim}")
```

### Example 3: Verifying Spectral BSD Identity

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)

# Compute spectral determinant
spectral_det = prover.compute_spectral_determinant(s=1)
print(f"det(I - M_E(1)) = {spectral_det}")

# Get L-function value
L_value = E.lseries().at1()
print(f"L(E,1) = {L_value}")

# Compute correction factor
c1 = prover.compute_c1()
print(f"c(1) = {c1}")

# Verify identity: det(I - M_E(1)) ≈ c(1) · L(E,1)
print(f"Ratio: {spectral_det / L_value if L_value != 0 else 'undefined'}")
```

### Example 4: Batch Analysis

```python
from src.spectral_finiteness import batch_prove_finiteness

curves = ['11a1', '14a1', '15a1', '17a1', '19a1']
results = batch_prove_finiteness(curves)

for label, result in results.items():
    if 'error' not in result:
        print(f"{label}: N={result['spectral_data']['conductor']}, "
              f"bound={result['global_bound']}")
```

## 🧪 Testing

The repository includes comprehensive tests:

```bash
# Run spectral BSD identity tests
python tests/test_spectral_bsd.py

# Run basic finiteness tests
python tests/test_finiteness.py
```

Test coverage includes:
- Spectral BSD identity verification
- Operator construction for different reduction types
- Kernel dimension computation
- Global bound computation
- Certificate generation
- Multi-curve batch processing

## 📖 Mathematical Background

### The Spectral Framework

The finiteness proof proceeds through three key steps:

1. **Operator Construction**: For each bad prime p|N, construct the spectral operator M_E,p(1) based on local representation theory

2. **Discreteness**: Verify that the spectral Selmer lattice Λ_spec is discrete:
   ```
   ∑_{p|N} dim ker(M_E,p(1)) < ∞
   ```

3. **Cocompactness**: Compute effective global bound:
   ```
   #Ш(E/ℚ) ≤ B = ∏_{p|N} p^(f_p)
   ```

### Spectral BSD Identity

The framework verifies the spectral BSD identity:
```
det(I - M_E(s)) = c(s) · L(E,s)
```

This identity connects:
- Left side: Spectral determinant (representation theory)
- Right side: L-function (analytic number theory)

### Local Operators by Reduction Type

| Reduction Type | Operator Size | Formula |
|---------------|---------------|---------|
| Good (f_p=0) | 1×1 | [1 - a_p + p] |
| Multiplicative (f_p=1) | 2×2 | Steinberg operator |
| Supercuspidal (f_p≥2) | f_p × f_p | Identity with modified corner |

## 🤝 Contributing

Contributions are welcome! Areas for enhancement:
- Additional certificate formats
- Optimization for large conductors
- Extended verification against databases
- Visualization tools

## 📄 License

This project implements mathematical algorithms described in the academic literature on spectral methods for elliptic curves.

## 📚 References

- Mota Burruezo, *Spectral Methods for Elliptic Curves*
- The framework is based on adèlic-spectral representation theory and the BSD conjecture

## 🔗 Links

- Repository: https://github.com/motanova84/algoritmo
- Issues: https://github.com/motanova84/algoritmo/issues

---

**Note**: This implementation requires SageMath for elliptic curve computations and number-theoretic functions.
