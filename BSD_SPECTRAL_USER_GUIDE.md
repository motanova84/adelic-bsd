# BSD Spectral User Guide

## Introduction

Welcome to the **BSD Spectral Framework** user guide. This document provides comprehensive instructions for installing, configuring, and using the `bsd-spectral` package.

**Version**: 0.3.0  
**License**: MIT  
**Repository**: https://github.com/motanova84/adelic-bsd

---

## Table of Contents

1. [Installation](#installation)
2. [Quick Start](#quick-start)
3. [Core Modules](#core-modules)
4. [Advanced Usage](#advanced-usage)
5. [API Reference](#api-reference)
6. [Examples](#examples)
7. [Troubleshooting](#troubleshooting)
8. [Contributing](#contributing)

---

## Installation

### Option 1: PyPI (Recommended)

```bash
pip install bsd-spectral
```

**With SageMath support** (Python < 3.12):
```bash
pip install bsd-spectral[sage]
```

**With development tools**:
```bash
pip install bsd-spectral[dev]
```

### Option 2: From Source

```bash
git clone https://github.com/motanova84/adelic-bsd.git
cd adelic-bsd
pip install -e .
```

### Option 3: SageMath Optional Package

```bash
# Within SageMath environment
sage -i bsd-spectral
```

### Prerequisites

**Required**:
- Python 3.9 or higher
- NumPy ≥ 1.24.3
- SciPy ≥ 1.10.1
- SymPy ≥ 1.12

**Optional (for full functionality)**:
- SageMath ≥ 9.8 (required for elliptic curve computations)
- Jupyter ≥ 1.0.0 (for notebooks)
- Matplotlib ≥ 3.7.2 (for visualizations)

---

## Quick Start

### Example 1: Prove Finiteness of Sha

```python
from bsd_spectral import prove_finiteness

# Prove finiteness for curve 11a1
result = prove_finiteness('11a1')

print(f"Finiteness proved: {result['finiteness_proved']}")
print(f"Global bound: {result['global_bound']}")
```

### Example 2: Verify Selmer Maps

```python
from bsd_spectral import verify_selmer_maps

# Verify Selmer map at primes 2, 3, 5
cert = verify_selmer_maps('37a1', primes=[2, 3, 5])

print(f"Verification passed: {cert['verification_passed']}")
```

### Example 3: Compute Beilinson-Bloch Regulator

```python
from bsd_spectral import compute_beilinson_bloch_regulator

# Compute regulator for rank 2 curve
reg = compute_beilinson_bloch_regulator('389a1')

print(f"Regulator: {reg:.6f}")
```

### Example 4: Vacuum Energy Equation

```python
from bsd_spectral import compute_vacuum_energy, find_minima

# Compute vacuum energy at R_Ψ = π
import math
energy = compute_vacuum_energy(math.pi)
print(f"E_vac(π) = {energy:.6f}")

# Find energy minima
minima = find_minima(n_range=(0, 5))
print(f"Minima at R_Ψ = π^n for n: {minima}")
```

---

## Core Modules

### 1. Finiteness Module

**Purpose**: Spectral finiteness proofs for Tate-Shafarevich groups

**Key Functions**:
- `prove_finiteness(curve_label)`: Prove Sha finiteness
- `batch_prove_finiteness(curve_labels)`: Batch processing
- `generate_finiteness_certificate(curve_label)`: Generate LaTeX certificate

**Example**:
```python
from bsd_spectral.finiteness import prove_finiteness

result = prove_finiteness('11a1')
if result['finiteness_proved']:
    print(f"Sha is finite with bound ≤ {result['global_bound']}")
```

### 2. Selmer Module

**Purpose**: Advanced Selmer map verification with p-adic cohomology

**Key Functions**:
- `verify_selmer_maps(curve, primes)`: Verify Selmer compatibility
- `batch_verify_selmer_maps(curves, primes)`: Batch verification
- `generate_selmer_certificate(curve)`: Generate certificate

**Example**:
```python
from bsd_spectral.selmer import verify_selmer_maps

cert = verify_selmer_maps('11a1', primes=[2, 3])
print(f"Map initialized: {cert['map_initialized']}")
print(f"Bloch-Kato satisfied: {cert['bloch_kato_satisfied']}")
```

### 3. Heights Module

**Purpose**: Beilinson-Bloch height pairings and regulators

**Key Functions**:
- `compute_beilinson_bloch_regulator(curve)`: Compute regulator
- `verify_height_compatibility(curve)`: Verify algebraic/analytic match
- `batch_verify_heights(curves)`: Batch processing
- `generate_height_certificate(curve)`: Generate certificate

**Example**:
```python
from bsd_spectral.heights import verify_height_compatibility

result = verify_height_compatibility('389a1')
print(f"Algebraic regulator: {result['algebraic_regulator']:.6f}")
print(f"Analytic regulator: {result['analytic_regulator']:.6f}")
print(f"Compatible: {result['compatible']}")
```

### 4. Vacuum Energy Module

**Purpose**: Fractal toroidal compactification and adelic phase structure

**Key Functions**:
- `compute_vacuum_energy(R_psi)`: Compute E_vac(R_Ψ)
- `find_minima(n_range)`: Find energy minima at R_Ψ = π^n
- `derive_frequency_f0()`: Derive fundamental frequency
- `compute_adelic_phase_structure(R_psi, primes)`: Adelic phases

**Example**:
```python
from bsd_spectral.vacuum_energy import (
    compute_vacuum_energy,
    generate_resonance_spectrum
)

# Compute vacuum energy
energy = compute_vacuum_energy(3.14159)
print(f"E_vac = {energy:.6f}")

# Generate resonance spectrum
spectrum = generate_resonance_spectrum(n_max=10)
for n, R_psi, energy in spectrum:
    print(f"n={n}: R_Ψ={R_psi:.4f}, E_vac={energy:.6f}")
```

---

## Advanced Usage

### Batch Processing

Process multiple curves efficiently:

```python
from bsd_spectral import batch_prove_finiteness

curves = ['11a1', '37a1', '389a1', '433a1']
results = batch_prove_finiteness(curves, output_dir='certificates')

print(f"Success rate: {results['success_rate']*100:.1f}%")
for curve, result in results['results'].items():
    print(f"{curve}: bound = {result['global_bound']}")
```

### Certificate Generation

Generate formal LaTeX certificates:

```python
from bsd_spectral import (
    generate_finiteness_certificate,
    generate_selmer_certificate,
    generate_height_certificate
)

# Finiteness certificate
cert1 = generate_finiteness_certificate('11a1', 'cert_11a1_finiteness.tex')

# Selmer certificate
cert2 = generate_selmer_certificate('37a1', 'cert_37a1_selmer.tex')

# Height certificate
cert3 = generate_height_certificate('389a1', 'cert_389a1_heights.tex')
```

### Custom Precision

Control numerical precision:

```python
from bsd_spectral.finiteness import prove_finiteness

# High precision
result = prove_finiteness('11a1', precision=50)

# Custom primes
result = prove_finiteness('11a1', primes=[2, 3, 5, 7, 11])
```

### Integration with LMFDB

Use the community validation system:

```bash
# Run community validation
python scripts/community_validation.py \
  --conductor-min 11 \
  --conductor-max 1000 \
  --limit 100 \
  --zenodo
```

---

## Examples

### Example 1: Complete Verification Pipeline

```python
from sage.all import EllipticCurve
from bsd_spectral import (
    prove_finiteness,
    verify_selmer_maps,
    verify_height_compatibility
)

# Define curve
E = EllipticCurve('389a1')
print(f"Curve: {E}")
print(f"Conductor: {E.conductor()}")
print(f"Rank: {E.rank()}")

# Step 1: Prove finiteness
fin_result = prove_finiteness(E)
print(f"\n1. Finiteness: {fin_result['finiteness_proved']}")

# Step 2: Verify Selmer
sel_result = verify_selmer_maps(E, primes=[2, 3])
print(f"2. Selmer verification: {sel_result['verification_passed']}")

# Step 3: Verify heights (rank ≥ 2)
if E.rank() >= 2:
    height_result = verify_height_compatibility(E)
    print(f"3. Height compatibility: {height_result['compatible']}")
```

### Example 2: Jupyter Notebook

See `examples/beilinson_bloch_demo.ipynb` for an interactive demonstration.

### Example 3: CI/CD Integration

```yaml
# .github/workflows/bsd-verification.yml
name: BSD Verification

on: [push]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'
      - name: Install dependencies
        run: |
          pip install bsd-spectral[dev]
      - name: Run verification
        run: |
          python -m bsd_spectral.finiteness --curves 11a1 37a1
```

---

## API Reference

See `API_REFERENCE.html` for complete API documentation generated with Sphinx.

**Quick Links**:
- [Finiteness API](./api/finiteness.html)
- [Selmer API](./api/selmer.html)
- [Heights API](./api/heights.html)
- [Vacuum Energy API](./api/vacuum_energy.html)

---

## Troubleshooting

### Issue: SageMath Not Found

**Problem**: `ImportError: No module named 'sage'`

**Solution**:
```bash
# Option 1: Install SageMath
conda install -c conda-forge sagemath

# Option 2: Use SageMath environment
sage -pip install bsd-spectral
```

### Issue: Numerical Precision Errors

**Problem**: Results differ slightly between runs

**Solution**: Increase precision
```python
result = prove_finiteness('11a1', precision=50)
```

### Issue: Slow Performance

**Problem**: Batch processing is slow

**Solution**: Use parallel processing (future feature)

### Issue: Certificate Generation Fails

**Problem**: LaTeX errors in certificate

**Solution**: Check LaTeX installation
```bash
# Install LaTeX
sudo apt-get install texlive-full  # Ubuntu
brew install --cask mactex          # macOS
```

---

## Contributing

We welcome contributions! Here's how to get started:

### Development Setup

```bash
git clone https://github.com/motanova84/adelic-bsd.git
cd adelic-bsd
pip install -e .[dev]
```

### Running Tests

```bash
# All tests
pytest tests/ -v

# Specific module
pytest tests/test_dR_uniformity.py -v

# With coverage
pytest tests/ --cov=bsd_spectral --cov-report=html
```

### Code Style

```bash
# Format code
black bsd_spectral/

# Lint
flake8 bsd_spectral/
```

### Submitting Changes

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/my-feature`
3. Commit changes: `git commit -m "Add my feature"`
4. Push to branch: `git push origin feature/my-feature`
5. Open a Pull Request

---

## Support

- **GitHub Issues**: https://github.com/motanova84/adelic-bsd/issues
- **GitHub Discussions**: https://github.com/motanova84/adelic-bsd/discussions
- **Documentation**: https://github.com/motanova84/adelic-bsd/blob/main/README.md

---

## Citation

If you use this package in your research, please cite:

```bibtex
@software{bsd_spectral,
  author = {Mota Burruezo, José Manuel},
  title = {BSD Spectral Framework: Computational Verification of the Birch-Swinnerton-Dyer Conjecture},
  year = {2025},
  version = {0.3.0},
  url = {https://github.com/motanova84/adelic-bsd}
}
```

---

## License

MIT License - see [LICENSE](../LICENSE) for details.

---

**Version**: 0.3.0  
**Last Updated**: 2025-10-27  
**Maintainer**: Mota Burruezo
