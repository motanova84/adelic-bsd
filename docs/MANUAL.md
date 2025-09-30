# Technical Manual: Spectral Finiteness Algorithm

## Installation

### Requirements
- **SageMath** ≥ 9.8
- **Python** ≥ 3.9
- Standard Python libraries (see `requirements.txt`)

### Using Conda (Recommended)

```bash
git clone https://github.com/motanova84/algoritmo.git
cd algoritmo
conda env create -f environment.yml
conda activate spectral-bsd
```

### Using pip

```bash
git clone https://github.com/motanova84/algoritmo.git
cd algoritmo
pip install -r requirements.txt
```

**Note**: SageMath must be installed separately if not using conda.

---

## Quick Start

### 1. Prove Finiteness for a Single Curve

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

# Create curve
E = EllipticCurve('11a1')

# Initialize prover
prover = SpectralFinitenessProver(E)

# Prove finiteness
result = prover.prove_finiteness()

print(f"Finiteness proved: {result['finiteness_proved']}")
print(f"Global bound: {result['global_bound']}")
```

### 2. Generate a Certificate

```python
# Generate text certificate
cert_text = prover.generate_certificate('text')
print(cert_text)

# Save to file
with open('certificate_11a1.txt', 'w') as f:
    f.write(cert_text)
```

### 3. Batch Processing

```python
from src.spectral_finiteness import batch_prove_finiteness

# Test multiple curves
curves = ['11a1', '37a1', '389a1']
results = batch_prove_finiteness(curves)

for label, result in results.items():
    print(f"{label}: bound = {result['global_bound']}")
```

---

## Running Examples

### Quick Demo

```bash
cd examples
sage -python quick_demo.py
```

This demonstrates the algorithm on several test curves.

### Comprehensive Demo

```bash
sage -python spectral_finiteness.py
```

This runs a comprehensive demonstration including:
- Multiple elliptic curves
- Certificate generation
- LMFDB comparison
- Statistical analysis

---

## Running Tests

### Basic Tests (No SageMath Required)

```bash
pytest tests/test_finiteness_basic.py -v
```

### Full Test Suite (Requires SageMath)

```bash
sage -python -m pytest tests/test_finiteness.py -v
```

Or run directly:

```bash
sage -python tests/test_finiteness.py
```

---

## Certificate Generation

### Generate Certificate for Single Curve

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
proof = prover.prove_finiteness()

# Generate text certificate
cert = prover.generate_certificate('text')

# Save certificate
with open('certificate_11a1.txt', 'w') as f:
    f.write(cert)
```

### Batch Certificate Generation

Use the provided script:

```bash
sage -python scripts/generate_all_certificates.py
```

This will generate certificates for all curves up to conductor 100.

---

## LMFDB Cross-Validation

The algorithm can be validated against known data from the L-functions and Modular Forms Database (LMFDB).

### Compare with Known Data

```python
from sage.all import EllipticCurve

E = EllipticCurve('11a1')

# Get known Sha from LMFDB/Sage
try:
    known_sha = E.sha().an()
    print(f"Known #Sha: {known_sha}")
except:
    print("Sha not available")

# Compute spectral bound
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()
print(f"Spectral bound: {result['global_bound']}")

# The spectral bound should be >= known Sha
assert result['global_bound'] >= known_sha
```

---

## Output Formats

### Text Certificate

Plain text format with:
- Curve information
- Conductor and rank
- Local spectral data for each prime
- Global bound
- Finiteness conclusion

### LaTeX Certificate (Planned)

Full LaTeX document with:
- Mathematical typesetting
- Detailed spectral operators
- Step-by-step verification
- References to theoretical framework

---

## Troubleshooting

### SageMath Not Found

Ensure SageMath is installed and accessible:

```bash
which sage
sage --version
```

### Import Errors

Make sure you're in the repository root:

```bash
cd /path/to/algoritmo
export PYTHONPATH="${PYTHONPATH}:$(pwd)"
```

### Memory Issues

For large batches of curves, increase memory limits or process in smaller batches.

---

## Advanced Usage

### Custom Conductor Range

```python
from sage.all import cremona_curves
from src.spectral_finiteness import SpectralFinitenessProver

# Get all curves up to conductor 50
for label in cremona_curves(50):
    E = EllipticCurve(label)
    prover = SpectralFinitenessProver(E)
    result = prover.prove_finiteness()
    print(f"{label}: {result['global_bound']}")
```

### Accessing Spectral Data

```python
E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

# Access detailed spectral data
spectral_data = result['spectral_data']
print(f"Conductor: {spectral_data['conductor']}")
print(f"Rank: {spectral_data['rank']}")

# Local data for each prime
for p, data in spectral_data['local_data'].items():
    print(f"Prime {p}:")
    print(f"  Reduction type: {data['reduction_type']}")
    print(f"  Kernel dimension: {data['kernel_dim']}")
    print(f"  Torsion bound: {data['torsion_bound']}")
```

---

## Performance Notes

- **Single curve**: < 1 second
- **Batch of 10 curves**: < 10 seconds
- **Conductor ≤ 100**: ~1-2 minutes

Performance depends on:
- Conductor size
- Reduction types at bad primes
- System specifications

---

## Citation

If you use this code in your research, please cite:

```bibtex
@software{mota_burruezo_2025_spectral_bsd,
  author       = {Mota Burruezo, José Manuel},
  title        = {Spectral Algorithm for BSD Conjecture},
  year         = 2025,
  publisher    = {GitHub},
  url          = {https://github.com/motanova84/algoritmo}
}
```

And the accompanying manuscript:

**"A Complete Spectral Reduction of the Birch and Swinnerton–Dyer Conjecture"**  
José Manuel Mota Burruezo (2025)

---

## Support

For issues, questions, or contributions:
- **GitHub Issues**: https://github.com/motanova84/algoritmo/issues
- **Discussions**: https://github.com/motanova84/algoritmo/discussions

---

## License

MIT License - see LICENSE file for details.
