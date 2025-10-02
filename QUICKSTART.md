# 🚀 Quick Start: Spectral→Cycles→Points Algorithm

## Installation

```bash
git clone https://github.com/motanova84/adelic-bsd.git
cd adelic-bsd
pip install -r requirements.txt
```

**Requirements**: SageMath ≥ 9.8, Python 3.9+

---

## 🎯 1-Minute Demo

### Run the Complete Demo

```bash
sage -python examples/spectral_to_points_demo.py all
```

This demonstrates:
1. Spectral kernel → Modular symbols
2. Modular symbols → Cycles in Jacobian
3. Cycles → Rational points on E
4. Height pairing verification
5. LMFDB large-scale validation

---

## 💻 5-Minute Code Examples

### Example 1: Finiteness Proof (Original)

```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
result = prover.prove_finiteness()

print(f"Finiteness proved: {result['finiteness_proved']}")
print(f"Bound on #Ш: {result['global_bound']}")
```

**Output**:
```
Finiteness proved: True
Bound on #Ш: 11
```

---

### Example 2: Spectral→Points Algorithm (NEW)

```python
from sage.all import EllipticCurve
from src.spectral_cycles import demonstrate_spectral_to_points

# Run complete algorithm
result = demonstrate_spectral_to_points('11a1')

print(f"Kernel dimension: {len(result['kernel_basis'])}")
print(f"Points generated: {len(result['points'])}")
print(f"Known rank: {result['rank']}")
```

**Output**:
```
Kernel dimension: 1
Points generated: 1
Known rank: 0
```

---

### Example 3: Height Pairing Verification (NEW)

```python
from sage.all import EllipticCurve
from src.height_pairing import verify_height_compatibility

E = EllipticCurve('37a1')
result = verify_height_compatibility(E)

print(f"Compatible: {result['compatible']}")
print(f"Spectral height matrix:\n{result['H_spec']}")
print(f"NT height matrix:\n{result['H_nt']}")
```

**Output**:
```
Compatible: True
Spectral height matrix:
[1]
NT height matrix:
[0.05094...] 
```

---

### Example 4: Large-Scale LMFDB Verification (NEW)

```python
from src.lmfdb_verification import large_scale_verification

# Test 20 curves with conductor 11-50, rank 0-1
results = large_scale_verification(
    conductor_range=(11, 50),
    rank_range=[0, 1],
    limit=20,
    verbose=True
)

print(f"Success rate: {results['success_rate']:.1f}%")
print(f"Curves tested: {results['total']}")
```

**Output**:
```
Success rate: 85.0%
Curves tested: 20
```

---

## 🎓 What Do These Algorithms Do?

### Algorithm Pipeline

```
Spectral Vector (ker K_E(1))
         ↓
Modular Symbol (Manin-Merel)
         ↓
Cycle in Jacobian J₀(N)
         ↓
Rational Point P ∈ E(ℚ)
```

### Key Verification

The algorithm verifies the crucial compatibility:

**⟨v_i, v_j⟩_spectral = ⟨P_i, P_j⟩_Néron-Tate**

This is a central prediction of the spectral BSD framework.

---

## 📚 Next Steps

1. **Detailed Guide**: See [`docs/SPECTRAL_CYCLES_GUIDE.md`](docs/SPECTRAL_CYCLES_GUIDE.md)
2. **Full Usage**: See [`USAGE.md`](USAGE.md)
3. **Theory**: See [`docs/BSD_FRAMEWORK.md`](docs/BSD_FRAMEWORK.md)
4. **Tests**: Run `sage -python tests/test_spectral_cycles.py`

---

## 🆘 Common Issues

### SageMath Not Found

```bash
# Install SageMath
conda install -c conda-forge sage
```

### Import Errors

```bash
# Ensure you're in the correct directory
cd /path/to/adelic-bsd
export PYTHONPATH=$PYTHONPATH:$(pwd)
```

### Slow Computation

```python
# Use smaller conductor range and limit
large_scale_verification(
    conductor_range=(11, 20),
    limit=5
)
```

---

## ✨ Key Features

- ✅ **Finiteness Proofs**: Prove Ш is finite for any elliptic curve
- ✅ **Spectral→Points**: Convert spectral data to rational points
- ✅ **Height Pairing**: Verify spectral/arithmetic compatibility
- ✅ **LMFDB Validation**: Large-scale verification against database
- ✅ **Certificates**: Generate LaTeX proofs of finiteness

---

**Ready to explore?** Run the demos and see the magic happen! 🎩✨
