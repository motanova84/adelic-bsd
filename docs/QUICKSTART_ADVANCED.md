# Quick Start: Advanced BSD Modules

This guide provides a quick introduction to the advanced BSD modules.

## Installation

Ensure you have the core framework installed:

```bash
cd /path/to/adelic-bsd
pip install -e .
```

Requires SageMath ≥ 9.5.

## 5-Minute Tutorial

### 1. Verify Selmer Map

```python
from sage.all import EllipticCurve
from src.cohomology import AdvancedSpectralSelmerMap

E = EllipticCurve('11a1')
selmer = AdvancedSpectralSelmerMap(E, p=2)

# Test on a vector
v = {'vector': [1, 0]}
result = selmer.phi_global(v)
print(f"Verified: {result['verified']}")
```

### 2. Verify Height Pairing

```python
from src.heights import verify_height_equality
from src.spectral_cycles import compute_kernel_basis

E = EllipticCurve('37a1')
kernel = compute_kernel_basis(E)
proof = verify_height_equality(E, kernel)
print(f"Heights equal: {proof['heights_equal']}")
```

### 3. Generate BSD Certificate

```python
from src.verification import generate_formal_certificate

E = EllipticCurve('11a1')
cert = generate_formal_certificate(E, save_to_file=True)
print(f"BSD proven: {cert['bsd_proven']}")
```

### 4. Batch Verification

```python
from src.verification import batch_prove_bsd

curves = ['11a1', '14a1', '15a1']
results = batch_prove_bsd(curves)

for label, cert in results.items():
    status = "✓" if cert.get('bsd_proven') else "✗"
    print(f"{label}: {status}")
```

## Run the Demo

```bash
sage -python examples/advanced_bsd_demo.py
```

This demonstrates all modules on example curves.

## Next Steps

- Read the full [Advanced Modules Documentation](ADVANCED_MODULES.md)
- Explore the [API Reference](ADVANCED_MODULES.md#api-reference)
- Run the [test suite](../tests/test_advanced_modules.py)
- Try [mass verification](ADVANCED_MODULES.md#mass-formal-proof)

## Common Use Cases

### Certificate Generation for Research

```python
from src.verification import FormalBSDProver

E = EllipticCurve('your_curve')
prover = FormalBSDProver(E, proof_level="full")
cert = prover.prove_bsd_completely()
prover.save_certificate(f"certificate_{E.cremona_label()}.json")
```

### Statistical Analysis

```python
from src.verification import MassFormalProof

mass = MassFormalProof()
results = mass.prove_entire_lmfdb(max_rank=2, max_curves=100)

stats = mass.get_statistics()
print(f"By rank: {stats['by_rank']}")
```

### Cohomology Analysis

```python
from src.cohomology.advanced_spectral_selmer import (
    construct_global_selmer_map,
    verify_spectral_to_selmer_compatibility
)

E = EllipticCurve('37a1')
kernel = compute_kernel_basis(E)

# Test all primes
compat = verify_spectral_to_selmer_compatibility(E, kernel, primes=[2,3,5,7])
print(f"All compatible: {compat['all_primes_compatible']}")
```

## Troubleshooting

**Q: Import errors for new modules?**

A: Ensure you're in the repository root and run:
```bash
export PYTHONPATH="${PYTHONPATH}:$(pwd)"
```

**Q: Tests failing?**

A: Some tests require SageMath. Run with:
```bash
sage -python -m pytest tests/test_advanced_modules.py
```

**Q: Numerical precision issues?**

A: Increase precision:
```python
selmer = AdvancedSpectralSelmerMap(E, p=2, precision=50)
height = AdvancedSpectralHeightPairing(E, p_adic_precision=100)
```

## Support

- Open an issue on [GitHub](https://github.com/motanova84/adelic-bsd/issues)
- Read the [Contributing Guide](../CONTRIBUTING.md)
- Check [existing issues](https://github.com/motanova84/adelic-bsd/issues)

---

**Happy verifying!** 🚀
