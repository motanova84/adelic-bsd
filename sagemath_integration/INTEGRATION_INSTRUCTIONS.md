# SageMath Integration Instructions

## Prerequisites

1. Fork SageMath repository on GitHub
2. Have git and SageMath installed locally
3. Familiarity with SageMath development workflow

## Step-by-Step Integration

### 1. Clone SageMath Repository

```bash
# Clone your fork
git clone https://github.com/YOUR_USERNAME/sage.git
cd sage

# Add upstream remote
git remote add upstream https://github.com/sagemath/sage.git

# Fetch latest changes
git fetch upstream
git checkout develop
git merge upstream/develop
```

### 2. Create Feature Branch

```bash
git checkout -b bsd-spectral-integration
```

### 3. Copy Module Files

```bash
# From the adelic-bsd repository root
cd /path/to/adelic-bsd/sagemath_integration

# Copy module files to SageMath
cp -r sage/schemes/elliptic_curves/bsd_spectral \
      /path/to/sage/src/sage/schemes/elliptic_curves/

# Copy documentation files
cp -r doc/en/reference/bsd_spectral \
      /path/to/sage/src/doc/en/reference/
```

### 4. Update Documentation Index

Edit `/path/to/sage/src/doc/en/reference/index.rst` to add:

```rst
.. toctree::

   ...existing entries...
   bsd_spectral/index
```

### 5. Run Tests

```bash
cd /path/to/sage

# Test the new module
./sage -t src/sage/schemes/elliptic_curves/bsd_spectral/*.py

# Expected output: All tests passed!
```

### 6. Build Documentation

```bash
cd src/doc
make html

# Check for any warnings or errors
# View docs at: _build/html/en/reference/bsd_spectral/index.html
```

### 7. Commit Changes

```bash
git add src/sage/schemes/elliptic_curves/bsd_spectral/
git add src/doc/en/reference/bsd_spectral/
git add src/doc/en/reference/index.rst

git commit -m "Add BSD spectral framework module

- Implements spectral-adelic approach to BSD
- Proves Sha(E/Q) finiteness under compatibility conditions
- Includes (dR) Fontaine-Perrin-Riou verification
- Includes (PT) Gross-Zagier + Yuan-Zhang-Zhang verification
- Complete documentation with 50+ doctests
- All tests passing

Reference: DOI 10.5281/zenodo.17236603
Author: José Manuel Mota Burruezo"
```

### 8. Push to Fork

```bash
git push -u origin bsd-spectral-integration
```

### 9. Create Pull Request

1. Go to https://github.com/YOUR_USERNAME/sage
2. Click "Compare & pull request" for your branch
3. Set base repository: `sagemath/sage`, base: `develop`
4. Set head repository: `YOUR_USERNAME/sage`, compare: `bsd-spectral-integration`
5. Copy content from `PULL_REQUEST.md` into the PR description
6. Submit the pull request

### 10. Respond to Reviewers

- Monitor the PR for comments and feedback
- Make requested changes promptly
- Re-run tests after each change
- Update documentation if needed

## Troubleshooting

### Tests Fail

If doctests fail:

1. Check the error message carefully
2. Verify SageMath version compatibility
3. Ensure all imports are available
4. Test interactively in Sage console

### Documentation Build Errors

If documentation fails to build:

1. Check RST syntax in .rst files
2. Verify autodoc can import modules
3. Check for missing references
4. Ensure LaTeX math is properly formatted

### Import Errors

If modules can't be imported:

1. Verify file paths are correct
2. Check `__init__.py` exists in each directory
3. Ensure lazy imports are properly configured
4. Test imports in Sage console

## Getting Help

- **SageMath Developer Guide**: https://doc.sagemath.org/html/en/developer/
- **Issue Tracker**: https://trac.sagemath.org/
- **Mailing List**: sage-devel@googlegroups.com
- **This Module**: institutoconsciencia@proton.me

## Timeline

Typical PR timeline:

- Week 1-2: Initial review and feedback
- Week 3-4: Address comments, make revisions
- Week 5-6: Final review and approval
- Week 7+: Merge into develop branch

Be patient and responsive to feedback!
