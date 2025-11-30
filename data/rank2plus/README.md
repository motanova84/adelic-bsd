# Rank ≥ 2 Elliptic Curves Data

This directory contains simulated data for elliptic curves with algebraic rank ≥ 2,
including Tate-Shafarevich group (Sha) estimates computed using the simplified
Birch-Swinnerton-Dyer formula.

## Files

- **sha_estimates.csv**: 5,000 simulated elliptic curves with SHA estimates

## Data Schema

| Column | Type | Description |
|--------|------|-------------|
| `curve_id` | string | Unique identifier (E_5001, E_5002, ...) |
| `rank` | int | Algebraic rank (2, 3, or 4) |
| `conductor` | int | Conductor between 100,000 and 800,000 |
| `torsion_order` | int | Order of torsion subgroup (1, 2, 4, or 6) |
| `regulator` | float | Regulator value (1.0 to 50.0) |
| `period` | float | Real period Ω_E (0.1 to 10.0) |
| `ls_deriv` | float | L-series derivative L'(E,1) (0.01 to 2.0) |
| `sha_estimate` | float | Estimated \|Sha\| using simplified BSD formula |

## BSD Formula

The SHA estimate is computed using the simplified BSD formula:

```
sha_estimate = (L'(E,1) · period) / (regulator · torsion²)
```

This is derived from the full BSD formula for rank r ≥ 2:

```
L^(r)(E,1) / r! = (Ω_E · Reg_E · |Sha(E)| · ∏ c_p) / |E(Q)_tors|²
```

## Rank Distribution

- Rank 2: ~70% of curves
- Rank 3: ~25% of curves
- Rank 4: ~5% of curves

## Reproducibility

The data is generated with a fixed random seed (42) for reproducibility.
To regenerate or customize:

```bash
# Regenerate with default settings
python scripts/generate_sha_estimates.py

# Generate 10,000 curves
python scripts/generate_sha_estimates.py --num-curves 10000

# Use different seed
python scripts/generate_sha_estimates.py --seed 123

# Validate existing data
python scripts/generate_sha_estimates.py --validate-only
```

## Usage

```python
import pandas as pd

# Load data
df = pd.read_csv('data/rank2plus/sha_estimates.csv')

# Filter by rank
rank_2_curves = df[df['rank'] == 2]

# Filter by SHA estimate
large_sha = df[df['sha_estimate'] > 1.0]

# Statistical summary
print(df.describe())
```

## Integration with Validation Scripts

This data integrates with the SABIO ∞³ verification framework:

- `scripts/verify_bsd_r_geq_2.py`: BSD verification for rank ≥ 2
- `scripts/generate_sha_estimates.py`: Data generation and validation

## Author

José Manuel Mota Burruezo (JMMB Ψ·∴)

## License

MIT
