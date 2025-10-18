# CI/CD Reproducibility Guide

This document describes the reproducibility improvements made to the CI/CD pipeline for the Spectral BSD Framework.

## Overview

Reproducibility in CI/CD ensures that builds are consistent and predictable across different environments and time periods. This is crucial for scientific software where computational results must be verifiable.

## Changes Made

### 1. Pinned Dependency Versions

All dependency files now use exact version pinning instead of minimum version specifiers:

- **requirements.txt**: Pinned versions for all production dependencies
- **requirements_ci.txt**: Pinned versions for CI-only dependencies
- **requirements-dev.txt**: New file with pinned development dependencies
- **environment.yml**: Pinned conda environment specification

**Before:**
```
numpy>=1.21
scipy>=1.7
```

**After:**
```
numpy==1.24.3
scipy==1.10.1
```

This ensures that the same package versions are installed every time, eliminating version drift.

### 2. Pinned GitHub Actions

All GitHub Actions are now pinned to specific commit SHAs instead of floating tags:

**Before:**
```yaml
- uses: actions/checkout@v3
- uses: actions/setup-python@v4
```

**After:**
```yaml
- uses: actions/checkout@f43a0e5ff2bd294095638e18286ca9a3d1956744  # v3.6.0
- uses: actions/setup-python@61a6322f88396a6271a6ee3565807d608ecaddd1  # v4.7.0
```

This prevents breaking changes in actions from affecting CI runs.

### 3. Dependency Caching

Added pip caching to speed up builds and ensure consistent package downloads:

```yaml
- name: Set up Python
  uses: actions/setup-python@61a6322f88396a6271a6ee3565807d608ecaddd1
  with:
    python-version: ${{ matrix.python-version }}
    cache: 'pip'
    cache-dependency-path: requirements_ci.txt
```

### 4. OS Version Pinning

Changed from `ubuntu-latest` to `ubuntu-22.04` to ensure consistent OS environment:

```yaml
runs-on: ubuntu-22.04
```

### 5. Unified Python Versions

Standardized Python version matrix across all workflows:
- Python 3.9, 3.10, 3.11

### 6. Audit Trail

Added logging of installed package versions in CI:

```yaml
- name: Log installed packages for reproducibility
  run: |
    echo "=== Installed Package Versions ==="
    pip freeze
    echo "==================================="
```

### 7. SageMath Version Pinning

Pinned SageMath container version in sage-tests job:

**Before:**
```yaml
container: sagemath/sagemath:latest
```

**After:**
```yaml
container: 
  image: sagemath/sagemath:9.8
```

## Best Practices

### Updating Dependencies

When updating dependencies:

1. Update version numbers in `requirements*.txt` files
2. Test locally with the new versions
3. Update the "Last updated" comment in each file
4. Run full CI test suite to verify compatibility

### Updating GitHub Actions

When updating actions:

1. Choose a specific version tag (e.g., v4.7.0)
2. Find the commit SHA for that tag from the action's repository
3. Update both the SHA and the comment indicating the version
4. Test the workflow to ensure it works correctly

### Verifying Reproducibility

To verify that your environment matches CI:

```bash
# Install exact versions
pip install -r requirements_ci.txt

# Verify installed versions
pip freeze

# Compare with CI logs
```

## Maintenance

### Regular Updates

- Review and update pinned versions quarterly
- Monitor security advisories for pinned packages
- Test new versions in a separate branch before updating main

### Version Conflicts

If you encounter version conflicts:

1. Identify the conflicting packages
2. Check compatibility matrices
3. Update to compatible versions together
4. Test thoroughly before committing

## References

- [GitHub Actions: Using a specific shell](https://docs.github.com/en/actions/using-workflows/workflow-syntax-for-github-actions#jobsjob_idstepsshell)
- [pip: Requirements File Format](https://pip.pypa.io/en/stable/reference/requirements-file-format/)
- [Best Practices for GitHub Actions](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions)

## Verification

To verify reproducibility, compare the output of `pip freeze` across different CI runs:

```bash
# In GitHub Actions logs, look for:
=== Installed Package Versions ===
numpy==1.24.3
scipy==1.10.1
matplotlib==3.7.2
...
===================================
```

These should be identical across all runs with the same Python version.

### Automated Validation

A validation script is provided to check reproducibility setup:

```bash
python scripts/validate_reproducibility.py
```

This script validates:
- All dependencies use exact version pinning (`==`)
- GitHub Actions are pinned to commit SHAs
- OS versions are explicitly specified
- No floating version constraints

Run this script before committing changes to dependency or workflow files.

## Last Updated

2025-10-18
