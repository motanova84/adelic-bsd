# BSD LMFDB 10,000 Curve Analysis Data

This directory contains output from the BSD experimental analysis
of 10,000+ LMFDB elliptic curves.

## Generated Files

When running `python scripts/estimate_sha.py`, the following files are created:

### `bsd_lmfdb_10000.csv`
Main output CSV with columns:
- `label` - LMFDB curve label (e.g., "11a1", "389a1")
- `conductor` - Conductor N_E
- `rank` - Algebraic rank r
- `torsion` - Order of torsion subgroup |E(Q)_tors|
- `tamagawa` - Product of Tamagawa numbers ∏c_p
- `regulator` - Néron-Tate regulator R_E
- `L_E_1` - L-function value L(E,1) or L^(r)(E,1)/r!
- `omega` - Real period Ω_E
- `sha_estimate` - Estimated |Ш(E)| via inverse BSD
- `error` - Distance from nearest integer
- `status` - Validation status (validated/pending/outlier/error)

### `bsd_analysis_results.json`
Detailed JSON with:
- Full results for each curve
- Batch statistics by rank
- Pattern detection results

### `qcal_beacon.json`
QCAL ∞³ validation beacon with:
- SHA3-256 hash of results
- Statistics summary
- Timestamp for reproducibility

## Usage

```bash
# Run full analysis (10,000 curves)
python scripts/estimate_sha.py

# Run smaller sample
python scripts/estimate_sha.py --curves 100

# Custom output directory
python scripts/estimate_sha.py --output-dir /path/to/output
```

## Key Statistics

The analysis focuses on:
- **Rank 0**: BSD proven (Euler systems)
- **Rank 1**: BSD proven (Gross-Zagier, Kolyvagin)
- **Rank ≥ 2**: Experimental validation (main focus)

Target success rate: ≥ 90% of curves with |Ш(E)| near perfect squares.

## Spectral Resonance

Pattern detection for ξ ∼ f₀ = 141.7001 Hz as per the QCAL framework.
