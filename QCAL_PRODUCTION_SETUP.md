# QCAL Production Setup Documentation

This document describes the production workflow infrastructure added to the Adelic-BSD repository.

## 🎯 Overview

The QCAL (Quantum Computational Adelic Logic) Production Cycle provides automated validation, aggregation, and deployment of the spectral BSD framework results.

## 📁 Files Added

### 1. Production Workflow
**File**: `.github/workflows/production-qcal.yml`

Automated workflow that runs every 4 hours and includes:
- Core validation with configurable precision
- Results aggregation
- Dataset publishing to HuggingFace
- Docker image building and registry push

**Key Features**:
- Scheduled execution: Every 4 hours via cron
- Manual trigger: Via `workflow_dispatch`
- Python 3.11 compatibility
- Pinned action versions for security
- Conditional execution based on event type

### 2. GitHub Copilot Instructions
**File**: `.github/copilot-instructions.md`

Comprehensive guidelines for GitHub Copilot to:
- Automatically detect and update workflows when scripts change
- Maintain Python version compatibility (3.9-3.13)
- Suggest GPU optimizations and parallelization strategies
- Manage dependencies and secrets
- Propose CI/CD improvements

### 3. Core Validation Script
**File**: `validate_v5_coronacion.py`

Validation script with the following capabilities:
- Configurable numerical precision (default: 30 decimal places)
- Core module integrity checks
- Repository structure validation
- Test suite discovery
- Reproducible random seed for numerical tests
- Comprehensive reporting

**Usage**:
```bash
python3 validate_v5_coronacion.py --precision 30
python3 validate_v5_coronacion.py --precision 50 --verbose
```

**Validation Checks**:
- ✓ Core modules existence (spectral_finiteness, spectral_cycles, etc.)
- ✓ Directory structure (src/, tests/, scripts/, .github/)
- ✓ Required files (README.md, requirements.txt, setup.py)
- ✓ Numerical precision tests (with reproducible seed)
- ✓ Test suite presence and count

### 4. Results Aggregation Script
**File**: `scripts/aggregate_results.py`

Aggregates validation results and generates reports:
- Creates organized results directory structure
- Collects certificates from multiple sources
- Catalogs all implemented modules
- Generates JSON and Markdown reports
- Timestamped output for historical tracking

**Usage**:
```bash
python3 scripts/aggregate_results.py
python3 scripts/aggregate_results.py --output custom/path
```

**Output Structure**:
```
results/
├── datasets/
├── certificates/
├── reports/
├── logs/
├── aggregated_results.json
├── results_YYYYMMDD_HHMMSS.json
└── SUMMARY.md
```

### 5. Docker Infrastructure
**File**: `Dockerfile`

Multi-stage Docker build for production deployment:
- Based on Python 3.11-slim
- Non-root user security
- Optimized layer caching
- Health check included
- Default validation command

**File**: `.dockerignore`

Optimizes Docker build by excluding:
- Git metadata
- Python cache files
- Development dependencies
- IDE configurations
- Test results

**Building and Running**:
```bash
# Build image
docker build -t qcal/production:latest .

# Run validation
docker run qcal/production:latest

# Run with custom precision
docker run qcal/production:latest python3 validate_v5_coronacion.py --precision 50
```

### 6. .gitignore Updates
**File**: `.gitignore`

Added exclusions for:
- `results/` - Generated result files
- `datasets/` - Dataset outputs

## 🔐 Required Secrets

For full production workflow functionality, configure these GitHub secrets:

### HuggingFace Integration
- `HF_TOKEN`: HuggingFace API token for dataset uploads
  - Scope: Write access to repositories
  - Repository: `motanova84/qcal-cloud`

### Docker Registry
- `DOCKERHUB_USERNAME`: Docker Hub username
- `DOCKERHUB_TOKEN`: Docker Hub access token
  - Scope: Read/Write access to repositories

**Note**: The workflow will gracefully skip steps if secrets are not configured.

## 🚀 Usage

### Manual Workflow Trigger

1. Go to GitHub Actions tab
2. Select "QCAL Production Cycle"
3. Click "Run workflow"
4. Choose branch and trigger

### Local Validation

Run the full validation pipeline locally:

```bash
# Install dependencies
pip install -r requirements.txt

# Run validation
python3 validate_v5_coronacion.py --precision 30

# Aggregate results
python3 scripts/aggregate_results.py

# Check results
cat results/SUMMARY.md
```

### Docker Deployment

```bash
# Build production image
docker build -t qcal/production:$(date +%Y%m%d) .

# Test locally
docker run --rm qcal/production:$(date +%Y%m%d)

# Push to registry (requires authentication)
docker push qcal/production:$(date +%Y%m%d)
```

## 🔄 Workflow Integration

The production workflow integrates with existing CI/CD:

1. **Scheduled Runs**: Every 4 hours
2. **Validation**: Precision-based core validation
3. **Aggregation**: Results collection and reporting
4. **Publishing**: HuggingFace dataset upload (scheduled only)
5. **Containerization**: Docker image build
6. **Deployment**: Registry push (scheduled only)

## 📊 Monitoring

### Workflow Status
Monitor workflow runs at:
```
https://github.com/motanova84/adelic-bsd/actions/workflows/production-qcal.yml
```

### Results Location
After successful runs, check:
- Local: `results/SUMMARY.md`
- HuggingFace: `motanova84/qcal-cloud` repository
- Docker: `qcal/production:RUN_NUMBER` images

## 🛠️ Maintenance

### Updating Dependencies
When updating `requirements.txt`:
1. GitHub Copilot will suggest workflow updates
2. Test locally with validation script
3. Rebuild Docker image to verify compatibility

### Adding New Validation Scripts
When creating new `validate_*` scripts:
1. Place in root or `scripts/` directory
2. Make executable: `chmod +x validate_*.py`
3. GitHub Copilot will suggest workflow integration

### GPU Optimization
For GPU-intensive operations:
1. Update workflow to use GPU runners
2. Add CUDA dependencies to Dockerfile
3. Follow Copilot suggestions for matrix strategies

## 🐛 Troubleshooting

### Validation Fails
```bash
# Check module imports
python3 -c "import src; print('OK')"

# Verify structure
python3 scripts/validate_structure.py

# Run with verbose
python3 validate_v5_coronacion.py --precision 30 --verbose
```

### Aggregation Issues
```bash
# Check write permissions
mkdir -p results && touch results/test.txt && rm results/test.txt

# Verify module discovery
find src -name "*.py" | wc -l
```

### Docker Build Fails
```bash
# Check dependencies
pip install -r requirements.txt

# Verify Dockerfile syntax
docker build --dry-run -t test .

# Build with verbose output
docker build --progress=plain -t qcal/production:test .
```

## 📈 Future Enhancements

Suggestions for extending the production workflow:

1. **Parallel Validation**: Matrix strategy for multiple precisions
2. **GPU Acceleration**: CUDA-enabled Docker images
3. **Result Archival**: Long-term storage integration
4. **Notification System**: Slack/Discord alerts for failures
5. **Performance Metrics**: Execution time tracking
6. **Artifact Upload**: GitHub Actions artifacts for debugging

## 📚 References

- **Problem Statement**: Original specification in issue
- **Copilot Instructions**: `.github/copilot-instructions.md`
- **Existing Workflows**: `.github/workflows/python-tests.yml`
- **Repository Structure**: `STRUCTURE_COMPLETE.md`

## ✅ Verification

All components have been tested and verified:
- ✅ Validation script runs successfully
- ✅ Aggregation generates proper reports
- ✅ YAML syntax validated
- ✅ Docker build succeeds
- ✅ No security vulnerabilities (CodeQL)
- ✅ Code review feedback addressed
- ✅ Reproducibility ensured (fixed random seed)

---

**Created**: 2025-10-20  
**Author**: GitHub Copilot Coding Agent  
**Version**: 1.0
