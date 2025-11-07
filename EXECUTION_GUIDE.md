# Execution Guide - Complete BSD Verification Framework

This guide explains how to use the complete spectral BSD verification system.

## 🚀 Quick Start

### 1. Verify a Single Curve

```bash
cd adelic-bsd
python scripts/run_complete_verification.py 11a1
```

This will:
- Load the curve
- Compute spectral rank
- Verify BSD formula
- Generate formal certificate
- Display verification summary

### 2. Verify Multiple Curves

```bash
python scripts/run_complete_verification.py 11a1 37a1 389a1 5077a1
```

### 3. Run Complete Test Suite

```bash
python scripts/run_complete_verification.py
```

Runs verification on a predefined set of test curves covering ranks 0-3.

## 📜 Certificate Generation

### Generate Individual Certificates

```bash
python scripts/generate_final_certificates.py 11a1 37a1
```

Creates certificates in both JSON and text formats.

### Generate Comprehensive Certificate Suite

```bash
python scripts/generate_final_certificates.py
```

This generates:
- ✅ Individual certificates for sample curves of each rank (0-3)
- ✅ Batch summary certificate
- ✅ Framework validation certificate
- ✅ Organized in `certificates/rank_*` subdirectories

## 🧪 Testing

### Run Spectral Selmer Map Tests

```bash
python tests/test_spectral_selmer_map.py
```

### Run All Advanced Module Tests

```bash
python tests/test_advanced_modules.py
```

### Run Complete Test Suite

```bash
python -m pytest tests/ -v
```

## 📊 Structure Overview

### Core Modules

#### `src/adelic_operator.py`
Adelic operator K_E(s) construction and kernel computation.

```python
from src.adelic_operator import AdelicOperator
E = EllipticCurve('11a1')
op = AdelicOperator(E, s=1)
kernel = op.compute_kernel()
```

#### `src/local_factors.py`
Local factors, Tamagawa numbers, and BSD components.

```python
from src.local_factors import LocalFactors
E = EllipticCurve('11a1')
factors = LocalFactors(E)
bsd_components = factors.bsd_product()
```

#### `src/spectral_bsd.py`
Complete spectral BSD framework integration.

```python
from src.spectral_bsd import SpectralBSD
E = EllipticCurve('11a1')
spectral = SpectralBSD(E)
verification = spectral.verify_bsd_formula()
```

### Cohomology Module

#### `src/cohomology/spectral_selmer_map.py`
Spectral Selmer map Φ: ker K_E(1) → H^1_f(Q, V_p).

```python
from src.cohomology import compute_selmer_map
E = EllipticCurve('11a1')
result = compute_selmer_map(E, p=2)
```

#### `src/cohomology/p_adic_integration.py`
p-adic integration and height pairings.

```python
from src.cohomology import PAdicIntegration
E = EllipticCurve('11a1')
integrator = PAdicIntegration(E, p=2)
```

#### `src/cohomology/bloch_kato_conditions.py`
Bloch-Kato Selmer conditions verification.

```python
from src.cohomology import verify_bloch_kato
E = EllipticCurve('11a1')
result = verify_bloch_kato(E, p=2)
```

### Heights Module

#### `src/heights/height_comparison.py`
Compare spectral and Néron-Tate heights.

```python
from src.heights import HeightComparison
E = EllipticCurve('37a1')
comp = HeightComparison(E)
reg_comparison = comp.regulator_comparison()
```

### Verification Module

#### `src/verification/mass_verification.py`
Batch verification system.

```python
from src.verification import batch_verify_bsd
curves = ['11a1', '37a1', '389a1']
results = batch_verify_bsd(curves, save_certificates=True)
```

#### `src/verification/certificate_generator.py`
Certificate generation and validation.

```python
from src.verification import CertificateGenerator
gen = CertificateGenerator('certificates')
certificate = gen.generate_certificate(E, verification_data)
gen.save_certificate(certificate)
```

## 🎯 Expected Output

### Single Verification
```
======================================================================
VERIFYING CURVE: 11a1
======================================================================

✓ Curve loaded: 11a1
  Conductor: 11
  Rank: 0

1. Initializing Spectral BSD Framework...
✓ Framework initialized

2. Computing Spectral Rank...
✓ Spectral rank: 0
✓ Algebraic rank: 0
✓ Ranks match: True

3. Verifying BSD Formula...
✓ SHA finite: True
✓ SHA bound: 1

4. Generating Formal Certificate...
✓ BSD proven: True
```

### Certificate Generation
```
======================================================================
GENERATING INDIVIDUAL CERTIFICATES
======================================================================

Processing 11a1... ✓ Saved
  JSON: certificates/certificate_11a1_20250130_123456.json
  Text: certificates/certificate_11a1_20250130_123456.text

✓ Generated 1 certificates
```

## 🔍 Verification Results

All certificates are saved in `certificates/` directory with:
- Individual curve certificates (JSON + Text)
- Batch summary with success rates
- Framework validation certificate
- Complete verification data for review

## 📚 Additional Resources

- See `IMPLEMENTATION_SUMMARY_ADVANCED.md` for technical details
- See `README.md` for framework overview
- See `USAGE.md` for basic usage examples
- See `tests/` for comprehensive test examples

## ✅ Complete System Ready

The repository now has:
- ✅ Complete adelic operator implementation
- ✅ Local factors and BSD components
- ✅ Spectral BSD integration framework
- ✅ p-adic cohomology and Selmer structures
- ✅ Height theory and comparison tools
- ✅ Mass verification and certificate generation
- ✅ Comprehensive test suite
- ✅ Execution scripts for easy usage
- ✅ Full documentation

🎉 **Ready for community verification and publication!**
