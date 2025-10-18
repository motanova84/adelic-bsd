# CI/CD Reproducibility Implementation - Summary

## Issue
[WIP] Corregir la implementación de CI/CD para garantizar la reproducibilidad

## Problem
The CI/CD pipeline had several reproducibility issues:
1. Dependencies used minimum version specifiers (>=) allowing version drift
2. GitHub Actions used floating tags (v3, v4) instead of pinned commits
3. OS versions used "latest" tags instead of specific versions
4. No dependency caching, leading to slower builds
5. Inconsistent Python version matrices across workflows
6. No audit trail of installed package versions
7. No validation mechanism for reproducibility setup
8. Missing security permissions on GitHub Actions workflows

## Solution Implemented

### 1. Dependency Version Pinning
**Files Modified:**
- `requirements.txt` - Pinned all production dependencies to exact versions
- `requirements_ci.txt` - Pinned CI dependencies
- `requirements-dev.txt` - Created new file with pinned development dependencies
- `environment.yml` - Pinned conda environment versions

**Impact:**
- Eliminates version drift over time
- Ensures consistent builds across all environments
- Makes debugging easier with known versions

### 2. GitHub Actions Security & Stability
**Files Modified:**
- `.github/workflows/python-tests.yml`
- `.github/workflows/python-package-conda.yml`
- `.github/workflows/validate-reproducibility.yml` (new)

**Changes:**
- Pinned all actions to commit SHAs (40-character hashes)
- Added inline comments showing version tags for reference
- Changed `ubuntu-latest` to `ubuntu-22.04`
- Pinned SageMath container from `:latest` to `:9.8`
- Added explicit `permissions: contents: read` blocks for security

**Impact:**
- Prevents supply chain attacks
- Protects against breaking changes in actions
- Follows GitHub security best practices

### 3. Build Performance Improvements
**Changes:**
- Added pip dependency caching with `cache: 'pip'`
- Added explicit cache configuration with content-based keys
- Reduces build time significantly after first run

### 4. Unified Python Version Matrix
**Before:** Mixed versions (3.8, 3.9, 3.10) vs (3.9, 3.10, 3.11)
**After:** Consistent (3.9, 3.10, 3.11) across all workflows

### 5. Audit Trail
**Changes:**
- Added "Log installed packages for reproducibility" step
- Runs `pip freeze` in every CI job
- Output visible in GitHub Actions logs

**Benefit:**
- Can trace exact versions installed in any build
- Easier debugging of version-related issues

### 6. Validation & Documentation
**New Files:**
- `docs/REPRODUCIBILITY.md` - Comprehensive guide (4.8KB)
- `scripts/validate_reproducibility.py` - Validation script (5.2KB)
- `.github/workflows/validate-reproducibility.yml` - Automated validation

**Updates:**
- `CONTRIBUTING.md` - Added reproducibility guidelines
- `README.md` - Added installation instructions with reproducibility notes
- `CHANGELOG.md` - Documented all changes

**Validation Script Features:**
- Checks all requirements files for exact version pinning
- Validates GitHub Actions are pinned to SHAs
- Ensures OS versions are explicitly specified
- Detects floating version constraints
- Exit code 0 on success, 1 on validation errors

### 7. Security Improvements
**Fixed CodeQL Alerts:**
- Added explicit permissions blocks to all workflow jobs
- Restricted GITHUB_TOKEN to minimum required permissions
- All jobs now use `permissions: contents: read`

**Result:** 0 security alerts after fixes

## Testing Performed

1. ✅ Validated all YAML syntax
2. ✅ Ran validation script successfully
3. ✅ Checked requirements file format
4. ✅ Verified workflow permissions
5. ✅ Ran CodeQL security scan (0 alerts)
6. ✅ Code review completed and feedback addressed

## Files Changed

```
.github/workflows/python-package-conda.yml     +47 -10
.github/workflows/python-tests.yml             +38 -11
.github/workflows/validate-reproducibility.yml  (new)
CHANGELOG.md                                   +16 lines
CONTRIBUTING.md                                +31 -1
README.md                                      +19 lines
docs/REPRODUCIBILITY.md                        (new, 4.8KB)
environment.yml                                +30 -14
requirements.txt                               +26 -11
requirements_ci.txt                            +16 -6
requirements-dev.txt                           (new)
scripts/validate_reproducibility.py           (new, 5.2KB)
```

Total: 12 files changed, ~610 insertions, ~53 deletions

## Reproducibility Guarantees

After these changes, the CI/CD pipeline now guarantees:

1. **Build Consistency**: Same dependencies installed every time
2. **Temporal Stability**: Builds work the same way months/years later
3. **Environment Consistency**: Same results across different machines
4. **Security**: Pinned actions prevent supply chain attacks
5. **Auditability**: Full record of installed versions in CI logs
6. **Validation**: Automated checks prevent configuration drift

## Maintenance

### Updating Dependencies
1. Update version in requirements file
2. Update "Last updated" comment
3. Run validation script: `python scripts/validate_reproducibility.py`
4. Test changes in CI

### Updating GitHub Actions
1. Find desired version tag
2. Get commit SHA for that tag
3. Update both SHA and inline comment
4. Test workflow

## Verification Commands

```bash
# Validate reproducibility setup
python scripts/validate_reproducibility.py

# Check for unpinned dependencies
grep -E '^[^#]*[><=~]{1,2}' requirements*.txt | grep -v '=='

# Compare installed versions with requirements
pip freeze | diff - <(grep -v '^#' requirements_ci.txt | grep -v '^-r')
```

## CI/CD Workflows

### 1. python-tests.yml
- Tests on Python 3.9, 3.10, 3.11
- Runs basic functionality tests
- Validates file structure
- Includes audit trail

### 2. python-package-conda.yml
- Basic tests without SageMath
- Full tests with SageMath 9.8 container
- Linting with flake8
- Package structure validation

### 3. validate-reproducibility.yml (NEW)
- Runs on changes to requirements or workflows
- Validates version pinning
- Checks for unpinned dependencies
- Verifies all required files exist

## Compliance

✅ All dependencies use exact version pinning (==)
✅ All GitHub Actions pinned to commit SHAs
✅ OS versions explicitly specified
✅ No floating version constraints
✅ Security permissions properly configured
✅ Comprehensive documentation provided
✅ Automated validation in place
✅ Code review completed
✅ Security scan passed (0 alerts)

## Next Steps for Users

1. Pull the changes
2. Review the new reproducibility documentation
3. Update local environments: `pip install -r requirements_ci.txt`
4. Verify setup: `python scripts/validate_reproducibility.py`

## References

- [GitHub Actions Security Best Practices](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions)
- [pip Requirements File Format](https://pip.pypa.io/en/stable/reference/requirements-file-format/)
- [Reproducible Builds](https://reproducible-builds.org/)

---

Implementation completed: 2025-10-18
Total commits: 5
Status: ✅ Ready for merge
