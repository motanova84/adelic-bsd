# 141.7001 Hz Gravitational Wave Analysis

## Overview

This directory contains the complete analysis framework for detecting and characterizing a potential coherent tone at 141.7001 Hz in gravitational wave detector data.

## Directory Structure

```
141hz/
├── PREREGISTRATION.md          # Blind preregistration protocol
├── analysis_plan.json          # Analysis parameters (JSON)
├── controls/
│   └── lines_exclusion.csv     # Instrumental lines to exclude
├── notebooks/
│   └── antenna_pattern.ipynb   # Antenna pattern analysis
├── bayes/
│   └── hierarchical_model.py   # Bayesian hierarchical inference
└── results/
    └── offsource_null.json     # Off-source null distribution
```

## Key Components

### 1. Preregistration Protocol

**File**: `PREREGISTRATION.md`

Establishes complete analysis methodology before examining data:
- Time window: [t₀-0.25s, t₀+0.25s] around coalescence
- Target frequency: 141.7001 Hz (±0.3 Hz) - **predefined**
- SNR method: Welch PSD (Nfft=2¹⁴, 50% overlap)
- Multiple events correction: Hierarchical Bayes model
- Instrumental lines exclusion
- Off-source: 10⁴ windows, time-slides: 200 offsets

### 2. Analysis Parameters

**File**: `analysis_plan.json`

Machine-readable analysis configuration:
- Frequency band: 20-1024 Hz
- PSD parameters: Hann window, 50% overlap
- Detectors: H1, L1, V1
- Statistical approach: Coherent Fisher mixture + Bayes Factor

### 3. Instrumental Controls

**File**: `controls/lines_exclusion.csv`

Documented exclusion of known instrumental artifacts:
- Mains harmonics (60 Hz, 120 Hz, ...)
- ADC sampling lines
- Violin modes (mechanical resonances)

### 4. Antenna Pattern Analysis

**File**: `notebooks/antenna_pattern.ipynb`

Computes expected amplitude ratios based on:
- Sky location (RA, Dec)
- Polarization angle
- Detector orientation (F⁺, F×)
- Arrival times

**Outputs**: Expected vs. observed amplitude ratios for coherence validation

### 5. Hierarchical Bayesian Model

**File**: `bayes/hierarchical_model.py`

Implements mixture model:
- H₀ (noise): SNR ~ N(0, 1)
- H₁ (signal): SNR ~ N(μ, σ²)
- Global parameter π: fraction of events with coherent tone

**Functions**:
- `loglik_event(snr, pi)`: Event-level log-likelihood
- `logpost(snr_list, pi)`: Posterior for π
- `bayes_factor(snr_list)`: Hierarchical Bayes Factor

### 6. Results and Validation

**File**: `results/offsource_null.json`

Stores:
- Off-source p-values (global and per-event)
- Time-slide background distributions
- Leave-one-out cross-validation results

## Usage

### Running the Analysis

```bash
# 1. Review preregistration
cat PREREGISTRATION.md

# 2. Load analysis parameters
python -c "import json; print(json.load(open('analysis_plan.json')))"

# 3. Compute Bayes Factor (example)
cd bayes
python hierarchical_model.py

# 4. Analyze antenna patterns
jupyter notebook notebooks/antenna_pattern.ipynb
```

### Workflow

1. **Preregister**: Commit `PREREGISTRATION.md` hash to Zenodo
2. **Load data**: LIGO/Virgo strain data around event times
3. **Apply controls**: Exclude instrumental lines from `lines_exclusion.csv`
4. **Compute SNRs**: Welch PSD, whitening, coherent combination
5. **Off-source**: Generate null distribution (10⁴ windows)
6. **Time-slides**: Cross-detector time shifts (200 offsets)
7. **Inference**: Hierarchical Bayes Factor
8. **Validate**: Antenna pattern consistency check

## Blind Analysis Protocol

**Critical**: All parameters are fixed **before** examining on-source data at 141.7001 Hz.

**Guarantee**: Prevents post-hoc selection bias by:
1. Predefining target frequency
2. Locking methodology via cryptographic hash
3. Using only off-source data for parameter tuning
4. Applying leave-one-out cross-validation

## Dependencies

```python
numpy
scipy
matplotlib
jupyter
# For LIGO data access:
# gwpy, lalsuite, pycbc (optional)
```

## References

- Abbott et al. (LIGO/Virgo). "GWTC-1: A Gravitational-Wave Transient Catalog". PRX, 2019.
- Cornish & Littenberg. "BayesWave: Bayesian Inference for GW Bursts". CQG, 2015.
- Chatziioannou et al. "Inferring the neutron star EOS from GW observations". PRD, 2017.

## Status

- [x] Preregistration protocol documented
- [x] Analysis plan defined (JSON)
- [x] Instrumental controls listed
- [x] Bayesian model implemented
- [x] Antenna pattern notebook created
- [ ] Apply to actual LIGO/Virgo data
- [ ] Compute final Bayes Factor
- [ ] Publish results

---

**Version**: 1.0  
**Date**: 2025-10-30  
**Contact**: JMMB Ψ · ∴
