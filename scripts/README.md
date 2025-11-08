# Scripts

Utility scripts for batch processing, certificate generation, verification, and SageMath PR preparation.

## 📝 Available Scripts

### 🔍 final_verification.sh ⭐ NEW

Comprehensive verification script that checks all critical aspects of the project before SageMath PR submission.

**Usage**:
```bash
./scripts/final_verification.sh
```

**What it checks**:
- ✅ GitHub Actions status
- ✅ Local CI-safe tests (4 tests)
- ✅ Local basic functionality tests (6 tests)
- ✅ Syntax check (flake8 on source code)
- ✅ Code quality metrics (informational)
- ✅ Critical files integrity
- ✅ Python version compatibility

**Expected output**: `🎉 ALL CRITICAL CHECKS PASSED! READY FOR SAGEMATH PR`

### 🚀 prepare_sagemath_pr.sh ⭐ NEW

Interactive script to prepare a pull request for the SageMath repository.

**Usage**:
```bash
# Default location (../sagemath-fork)
./scripts/prepare_sagemath_pr.sh

# Custom location
export SAGEMATH_DIR=/path/to/sagemath-fork
./scripts/prepare_sagemath_pr.sh
```

**What it does**:
1. Checks/clones SageMath repository
2. Fetches latest changes from upstream
3. Creates feature branch `bsd-spectral-framework`
4. Copies module files, documentation, and tests
5. Runs SageMath tests (optional)
6. Creates comprehensive commit
7. Provides push instructions

**Prerequisites**: SageMath fork cloned (or the script will guide you)

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

## 🔄 Recommended Workflow

### For Development and Testing
```bash
# 1. Make changes to code
vim src/your_file.py

# 2. Run verification to ensure nothing broke
./scripts/final_verification.sh

# 3. If all checks pass, commit
git add .
git commit -m "Your descriptive message"
git push
```

### For SageMath PR Submission
```bash
# 1. Ensure all tests pass
./scripts/final_verification.sh
# Expected: ✅ ALL CRITICAL CHECKS PASSED!

# 2. Prepare SageMath PR
./scripts/prepare_sagemath_pr.sh
# Follow the interactive prompts

# 3. Push to your fork (instructions will be provided)
cd ../sagemath-fork
git push -u YOUR_FORK bsd-spectral-framework

# 4. Create PR on GitHub
# - Go to https://github.com/sagemath/sage
# - Click "New Pull Request"
# - Use template from ../SAGEMATH_PR.md
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
