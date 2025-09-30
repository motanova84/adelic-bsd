# Scripts

Utility scripts for batch processing and certificate generation.

## 📝 Available Scripts

### generate_all_certificates.py

Batch generate finiteness certificates for multiple elliptic curves.

**Usage**:

```bash
# Generate certificates for all curves with conductor ≤ 50 (default)
sage -python scripts/generate_all_certificates.py

# Generate for conductor ≤ 100
sage -python scripts/generate_all_certificates.py --conductor 100

# Generate for specific curves
sage -python scripts/generate_all_certificates.py --curves 11a1 37a1 389a1

# Specify output directory
sage -python scripts/generate_all_certificates.py --output my_certificates/
```

**Options**:
- `--conductor N`: Process all curves with conductor ≤ N
- `--curves LABEL1 LABEL2 ...`: Process specific curve labels
- `--output DIR`: Output directory (default: certificates/)

**Output**:
- Creates one certificate file per curve: `certificate_LABEL.txt`
- Prints summary statistics
- Reports any errors encountered

**Example**:

```bash
$ sage -python scripts/generate_all_certificates.py --conductor 20

🚀 Generating certificates for curves with conductor ≤ 20
📁 Output directory: certificates/
======================================================================
✓ 11a1: Certificate generated (bound=11)
✓ 11a2: Certificate generated (bound=5)
✓ 11a3: Certificate generated (bound=1)
✓ 14a1: Certificate generated (bound=7)
...
======================================================================
📊 SUMMARY:
   Total curves processed: 15
   Successful: 15
   Failed: 0
   Success rate: 100.0%

📁 Certificates saved in: certificates/
```

---

## 🔧 Adding New Scripts

To add a new utility script:

1. Create the script in this directory
2. Add a main() function with argument parsing
3. Document usage in this README
4. Add tests if appropriate
5. Make the script executable: `chmod +x script_name.py`

**Template**:

```python
#!/usr/bin/env python3
"""
Brief description of what the script does
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Script description')
    parser.add_argument('--option', help='Option help')
    args = parser.parse_args()
    
    # Script logic here
    pass


if __name__ == "__main__":
    main()
```

---

## 📋 Planned Scripts

Future utility scripts that could be added:

- **compare_with_lmfdb.py**: Automated LMFDB data comparison
- **batch_validate.py**: Validate existing certificates
- **export_results.py**: Export results to CSV/JSON
- **benchmark.py**: Performance benchmarking across curve ranges
- **latex_certificate_gen.py**: Generate full LaTeX certificates (currently text only)

---

## 🐛 Troubleshooting

### SageMath not found

Make sure you're running scripts with `sage -python`:

```bash
sage -python scripts/generate_all_certificates.py
```

### Import errors

Ensure you're in the repository root when running scripts:

```bash
cd /path/to/algoritmo
sage -python scripts/generate_all_certificates.py
```

### Memory issues

For large conductor ranges, process in smaller batches:

```bash
sage -python scripts/generate_all_certificates.py --conductor 50
sage -python scripts/generate_all_certificates.py --conductor 100  # then 51-100
```

---

## 📚 See Also

- [docs/MANUAL.md](../docs/MANUAL.md) - Complete technical manual
- [examples/](../examples/) - Interactive examples
- [tests/](../tests/) - Test suite

---

For questions or issues, please open a GitHub issue.
