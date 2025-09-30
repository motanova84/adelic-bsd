# Algoritmo Espectral - Mota Burruezo Framework

A spectral algorithm for proving finiteness of Tate–Shafarevich groups of elliptic curves over ℚ.

## 📋 Overview

This repository implements a spectral approach to proving the finiteness of the Tate–Shafarevich group Ш(E/ℚ) for elliptic curves. The framework is based on adèlic-spectral methods and provides:

- **Spectral finiteness proofs** for elliptic curves
- **Effective bounds** on the order of Ш(E/ℚ)
- **Certificate generation** in text and LaTeX formats
- **Batch processing** for multiple curves
- **Local spectral data** computation for primes of bad reduction

## 🚀 Quick Start

### Installation

#### Using Conda (Recommended)

```bash
# Clone the repository
git clone https://github.com/motanova84/algoritmo.git
cd algoritmo

# Create conda environment
conda env create -f environment.yml
conda activate algoritmo-spectral
```

#### Using pip

```bash
# Install dependencies
pip install -r requirements.txt

# Install the package
pip install -e .
```

### Basic Usage

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

# Create a curve
E = EllipticCurve('11a1')

# Prove finiteness
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

print(f"Finiteness proved: {result['finiteness_proved']}")
print(f"Global bound: {result['global_bound']}")
```

### Run the Demo

```bash
# Quick demo with sample curves
python examples/quick_demo.py

# Or use the command-line tool
spectral-demo
```

## 📁 Repository Structure

```
algoritmo/
├── src/                        # Main source code
│   ├── spectral_finiteness.py  # Core algorithm implementation
│   └── __init__.py
├── examples/                   # Example scripts and demos
│   ├── quick_demo.py           # Quick demonstration
│   └── __init__.py
├── tests/                      # Test suite
│   ├── test_finiteness.py      # Unit tests
│   └── __init__.py
├── spectral_finiteness.py      # Standalone version with extended examples
├── requirements.txt            # Python dependencies
├── environment.yml             # Conda environment specification
├── setup.py                    # Package installation script
└── README.md                   # This file
```

## 🧪 Testing

Run the test suite:

```bash
# Run all tests
pytest tests/

# Run specific test file
python tests/test_finiteness.py

# Run with verbose output
pytest -v tests/
```

## 📚 Features

### Spectral Finiteness Prover

The core `SpectralFinitenessProver` class provides:

- **`prove_finiteness()`**: Main method that proves finiteness and computes bounds
- **`generate_certificate(format='text')`**: Generate human-readable certificates
- **Local spectral data**: Computation of spectral operators for each bad prime
- **Effective bounds**: Computable bounds on #Ш(E/ℚ)

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

# LaTeX certificate (future feature)
cert_latex = prover.generate_certificate('latex')
```

## 🔬 Mathematical Background

The algorithm implements a spectral approach to proving finiteness of Ш(E/ℚ) based on:

1. **Local spectral operators** M_E,p(s) for primes of bad reduction
2. **Kernel dimension analysis** for computing local torsion bounds
3. **Global bounds** obtained by multiplying local contributions
4. **Reduction type classification**:
   - Good reduction (trivial contribution)
   - Multiplicative reduction (Steinberg representation)
   - Supercuspidal reduction (higher conductor exponent)

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

### Example 2: Batch Analysis

```python
from src.spectral_finiteness import batch_prove_finiteness

# Analyze curves with small conductors
curves = [f'{N}a1' for N in [11, 14, 15, 17, 19, 20, 21, 24, 26, 27]]
results = batch_prove_finiteness(curves)

successful = sum(1 for r in results.values() if 'error' not in r)
print(f"Successfully proved finiteness for {successful}/{len(curves)} curves")
```

## 🔧 Development

### Running Tests

```bash
# Install development dependencies
pip install -e .[dev]

# Run tests with coverage
pytest --cov=src tests/

# Run linting
flake8 src/ tests/ examples/
```

### Contributing

Contributions are welcome! Please:

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

## 📖 References

This implementation is based on the Mota Burruezo spectral framework for studying Tate–Shafarevich groups using adèlic-spectral methods.

## 📄 License

MIT License - see LICENSE file for details

## 👤 Author

Mota Burruezo

## 🙏 Acknowledgments

- SageMath community for the excellent mathematical software
- LMFDB for elliptic curve data verification

## ⚠️ Notes

- This is a research implementation and is under active development
- The algorithm works for elliptic curves over ℚ
- Bounds are effective but may not always be sharp
- For curves with very large conductors, computation may be slow