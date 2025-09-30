# API Reference - Spectral Finiteness Framework

## Overview

This document provides detailed API reference for all public classes and functions in the spectral finiteness framework.

## Table of Contents

- [Main Interface](#main-interface)
  - [SpectralFinitenessProver](#spectralfinitennessprover)
  - [Convenience Functions](#convenience-functions)
- [Spectral Operator Module](#spectral-operator-module)
- [Kernel Computation Module](#kernel-computation-module)
- [Global Bound Module](#global-bound-module)
- [Certificate Generator Module](#certificate-generator-module)

---

## Main Interface

### SpectralFinitenessProver

Main class for proving finiteness of Ш(E/ℚ) using spectral methods.

```python
class SpectralFinitenessProver(E)
```

#### Constructor

**Parameters:**
- `E` (EllipticCurve): An elliptic curve over ℚ

**Example:**
```python
from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver

E = EllipticCurve('11a1')
prover = SpectralFinitenessProver(E)
```

#### Methods

##### `prove_finiteness()`

Prove finiteness of Ш(E/ℚ) and compute effective bounds.

**Returns:**
- `dict`: Dictionary containing:
  - `finiteness_proved` (bool): Always True
  - `global_bound` (int): Effective bound B on #Ш
  - `spectral_data` (dict): Complete spectral analysis
  - `curve_label` (str): Curve identifier

**Example:**
```python
result = prover.prove_finiteness()
print(f"Finiteness: {result['finiteness_proved']}")
print(f"Bound: {result['global_bound']}")
```

##### `construct_spectral_operator(p, s=1)`

Construct the spectral operator M_E,p(s) at prime p.

**Parameters:**
- `p` (int): Prime number
- `s` (numeric, optional): Complex parameter (default: 1)

**Returns:**
- `Matrix`: The spectral operator M_E,p(s)

**Example:**
```python
M_11 = prover.construct_spectral_operator(11)
print(M_11)
```

##### `compute_kernel_dimension(operator)`

Compute the dimension of ker(M_E,p(1)).

**Parameters:**
- `operator` (Matrix): Spectral operator matrix

**Returns:**
- `int`: Dimension of the kernel

**Example:**
```python
M_p = prover.construct_spectral_operator(11)
dim = prover.compute_kernel_dimension(M_p)
print(f"Kernel dimension: {dim}")
```

##### `compute_global_bound()`

Compute the global bound B on #Ш(E/ℚ).

**Returns:**
- `int`: Global bound B = ∏_p b_p

**Example:**
```python
bound = prover.compute_global_bound()
print(f"#Ш ≤ {bound}")
```

##### `compute_spectral_determinant(s=1)`

Compute the spectral determinant det(I - M_E(s)).

**Parameters:**
- `s` (numeric, optional): Complex parameter (default: 1)

**Returns:**
- `numeric`: The determinant value

**Theory:**
This is the key quantity in the spectral BSD identity:
```
det(I - M_E(s)) = c(s) · L(E,s)
```

**Example:**
```python
det = prover.compute_spectral_determinant(s=1)
L_value = E.lseries().at1()
ratio = det / L_value
```

##### `compute_c1()`

Compute the correction factor c(1) in the spectral BSD identity.

**Returns:**
- `numeric`: Correction factor c(1)

**Theory:**
The spectral BSD identity at s=1:
```
det(I - M_E(1)) = c(1) · L(E,1)
```

**Example:**
```python
c1 = prover.compute_c1()
print(f"Correction factor: {c1}")
```

##### `generate_certificate(format='text')`

Generate a finiteness certificate.

**Parameters:**
- `format` (str): Certificate format ('text', 'latex', or 'json')

**Returns:**
- `str`: Certificate in specified format

**Example:**
```python
cert_text = prover.generate_certificate('text')
cert_latex = prover.generate_certificate('latex')
cert_json = prover.generate_certificate('json')
```

### Convenience Functions

#### `prove_finiteness_for_curve(curve_label)`

Prove finiteness for a curve by its label.

**Parameters:**
- `curve_label` (str): Cremona label (e.g., '11a1')

**Returns:**
- `dict`: Proof results (same as `prove_finiteness()`)

**Example:**
```python
from src.spectral_finiteness import prove_finiteness_for_curve

result = prove_finiteness_for_curve('11a1')
```

#### `batch_prove_finiteness(curve_labels)`

Prove finiteness for multiple curves.

**Parameters:**
- `curve_labels` (list): List of Cremona labels

**Returns:**
- `dict`: Dictionary mapping labels to results

**Example:**
```python
from src.spectral_finiteness import batch_prove_finiteness

curves = ['11a1', '14a1', '15a1']
results = batch_prove_finiteness(curves)
```

---

## Spectral Operator Module

### SpectralOperatorBuilder

Class for constructing spectral operators M_E,p(s).

```python
from src.spectral_operator import SpectralOperatorBuilder

builder = SpectralOperatorBuilder(E)
```

#### Methods

##### `construct_operator(p, s=1)`

Construct M_E,p(s) at prime p.

**Parameters:**
- `p` (int): Prime number
- `s` (numeric): Complex parameter

**Returns:**
- `Matrix`: Spectral operator

**Operator Forms:**
- Good reduction: 1×1 matrix [1 - a_p + p]
- Multiplicative: 2×2 Steinberg operator
- Supercuspidal: f_p × f_p matrix

##### `compute_spectral_determinant(s=1)`

Compute det(I - M_E(s)) for the global operator.

**Parameters:**
- `s` (numeric): Complex parameter

**Returns:**
- `numeric`: Determinant value

### Convenience Function

#### `construct_spectral_operator(E, p, s=1)`

Direct operator construction without creating builder object.

**Example:**
```python
from src.spectral_operator import construct_spectral_operator

E = EllipticCurve('11a1')
M_11 = construct_spectral_operator(E, 11, s=1)
```

---

## Kernel Computation Module

### KernelAnalyzer

Analyzes kernels of spectral operators.

```python
from src.kernel_computation import KernelAnalyzer

analyzer = KernelAnalyzer(E)
```

#### Methods

##### `compute_kernel_dimension(operator)`

Compute dim ker(M_E,p(1)).

**Parameters:**
- `operator` (Matrix): Spectral operator

**Returns:**
- `int`: Kernel dimension

##### `compute_kernel_basis(operator)`

Compute basis vectors for ker(M_E,p(1)).

**Parameters:**
- `operator` (Matrix): Spectral operator

**Returns:**
- `list`: List of basis vectors

##### `analyze_local_kernel(p, operator)`

Comprehensive kernel analysis at prime p.

**Parameters:**
- `p` (int): Prime number
- `operator` (Matrix): Spectral operator

**Returns:**
- `dict`: Analysis including dimension, basis, rank

##### `verify_discreteness(local_operators)`

Verify discreteness condition for Λ_spec.

**Parameters:**
- `local_operators` (dict): Dictionary {p: M_E,p(1)}

**Returns:**
- `dict`: Verification results

### SpectralSelmerAnalyzer

Analyzes the spectral Selmer lattice Λ_spec.

```python
from src.kernel_computation import SpectralSelmerAnalyzer

analyzer = SpectralSelmerAnalyzer(E)
```

#### Methods

##### `analyze_spectral_lattice(local_operators)`

Comprehensive lattice analysis.

**Parameters:**
- `local_operators` (dict): Dictionary {p: M_E,p(1)}

**Returns:**
- `dict`: Lattice properties and finiteness criteria

### Convenience Functions

#### `compute_kernel_dimension(operator)`

Quick kernel dimension computation.

#### `compute_kernel_basis(operator)`

Quick kernel basis computation.

---

## Global Bound Module

### GlobalBoundComputer

Computes effective bounds on #Ш(E/ℚ).

```python
from src.global_bound import GlobalBoundComputer

computer = GlobalBoundComputer(E)
```

#### Methods

##### `compute_local_torsion_bound(p)`

Compute local bound b_p at prime p.

**Parameters:**
- `p` (int): Prime number

**Returns:**
- `int`: Local bound b_p = p^(f_p)

**Formula:**
- Good reduction (f_p=0): b_p = 1
- Multiplicative (f_p=1): b_p = p
- Supercuspidal (f_p≥2): b_p = p^(f_p)

##### `compute_global_bound()`

Compute global bound B = ∏_p b_p.

**Returns:**
- `int`: Global bound

##### `compute_detailed_bound_data()`

Get comprehensive bound information.

**Returns:**
- `dict`: Detailed bound data including formula

### BoundVerifier

Verifies bounds against known data.

```python
from src.global_bound import BoundVerifier

verifier = BoundVerifier(E)
```

#### Methods

##### `verify_bound_validity()`

Verify computed bound against known #Ш.

**Returns:**
- `dict`: Verification results

##### `compare_with_bsd_prediction()`

Compare with BSD conjecture prediction.

**Returns:**
- `dict`: Comparison data

### Convenience Functions

#### `compute_global_bound(E)`

Quick global bound computation.

**Example:**
```python
from src.global_bound import compute_global_bound

E = EllipticCurve('11a1')
bound = compute_global_bound(E)
```

#### `compute_local_bound(E, p)`

Quick local bound computation.

---

## Certificate Generator Module

### CertificateGenerator

Generates finiteness certificates in various formats.

```python
from src.certificate_generator import CertificateGenerator

generator = CertificateGenerator(E)
```

#### Methods

##### `generate(proof_data, format='text')`

Generate certificate in specified format.

**Parameters:**
- `proof_data` (dict): Proof results from `prove_finiteness()`
- `format` (str): 'text', 'latex', or 'json'

**Returns:**
- `str`: Certificate string

##### `generate_text_certificate(proof_data)`

Generate human-readable text certificate.

**Parameters:**
- `proof_data` (dict): Proof results

**Returns:**
- `str`: Text certificate

##### `generate_latex_certificate(proof_data)`

Generate publication-ready LaTeX certificate.

**Parameters:**
- `proof_data` (dict): Proof results

**Returns:**
- `str`: LaTeX document

##### `generate_json_certificate(proof_data)`

Generate machine-readable JSON certificate.

**Parameters:**
- `proof_data` (dict): Proof results

**Returns:**
- `str`: JSON string

### FinitenessCache

Stores and validates proof results.

```python
from src.certificate_generator import FinitenessCache

cache = FinitenessCache(proof_data)
```

#### Methods

##### `validate()`

Validate completeness and consistency of proof data.

**Returns:**
- `dict`: Validation results

### Convenience Function

#### `generate_certificate(E, proof_data, format='text')`

Direct certificate generation.

**Example:**
```python
from src.certificate_generator import generate_certificate

cert = generate_certificate(E, proof_data, format='latex')
```

---

## Type Reference

### Proof Data Dictionary

The `prove_finiteness()` method returns a dictionary with this structure:

```python
{
    'finiteness_proved': bool,      # Always True
    'global_bound': int,             # Bound B on #Ш
    'curve_label': str,              # Curve identifier
    'spectral_data': {
        'conductor': int,            # Conductor N
        'rank': int,                 # Mordell-Weil rank
        'local_data': {
            p: {                     # For each bad prime p
                'operator': Matrix,  # M_E,p(1)
                'kernel_dim': int,   # dim ker(M_E,p(1))
                'torsion_bound': int,# b_p
                'reduction_type': str,# 'good', 'multiplicative', or 'supercuspidal'
                'prime': int         # p
            }
        }
    }
}
```

### Verification Data Dictionary

The `verify_discreteness()` method returns:

```python
{
    'is_discrete': bool,             # Always True for elliptic curves
    'total_kernel_dimension': int,   # ∑_p dim ker(M_E,p(1))
    'bad_primes_count': int,         # Number of bad primes
    'per_prime_dimensions': dict,    # {p: kernel_dim}
    'discreteness_proved': bool      # True
}
```

---

## Error Handling

All functions handle errors gracefully:

- Invalid curve labels return error dictionaries in batch operations
- Missing data raises appropriate exceptions with descriptive messages
- Numerical issues in L-function computation are caught and reported

**Example:**
```python
results = batch_prove_finiteness(['11a1', 'invalid'])
# results['invalid'] will contain {'error': 'error message'}
```

---

## Performance Considerations

- **Small conductors (N < 100)**: Fast (< 1 second)
- **Medium conductors (100 ≤ N < 1000)**: Moderate (1-10 seconds)
- **Large conductors (N ≥ 1000)**: Slow (> 10 seconds)

For batch processing, consider parallelization for large datasets.

---

## Notes

1. All methods require SageMath to be installed
2. Curves must be defined over ℚ
3. Bounds are always valid upper bounds (may not be sharp)
4. Certificate generation preserves all computed data
5. The spectral BSD identity is verified up to normalization constants

---

For usage examples, see `USAGE.md`. For architectural overview, see `README.md`.
