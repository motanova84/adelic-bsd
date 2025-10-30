# Documentation

This directory contains comprehensive documentation for the Spectral BSD Framework.

## 📚 Documentation Files

### [MANUAL.md](MANUAL.md)
**Technical usage guide** - Complete guide for installing, using, and troubleshooting the code.

**Contents**:
- Installation instructions (conda and pip)
- Quick start examples
- Running tests
- Certificate generation
- LMFDB cross-validation
- Advanced usage and performance notes
- Citation guidelines

**Audience**: Researchers, developers, and users who want to run the code

---

### [BSD_FRAMEWORK.md](BSD_FRAMEWORK.md)
**Theoretical foundations** - Detailed explanation of the mathematical framework with explicit paper references.

**Contents**:
- Core theorems (4.3, 6.1, 8.3) and their implementation
- Outstanding hypotheses (dR) and (PT)
- Spectral descent framework
- Computational validation strategy
- Mathematical rigor checklist
- Paper-to-code mapping
- Comparison with other BSD approaches
- Open problems and further reading

**Audience**: Mathematicians, theoretical researchers, and anyone interested in the mathematical foundations

---

### [HPC_SOLVER.md](HPC_SOLVER.md)
**High-Performance Computing framework** - Conceptual documentation for quantum many-body physics simulations.

**Contents**:
- Exact Diagonalization method for quantum systems
- GPU acceleration with CUDA/cuBLAS/cuSOLVER
- Technical architecture and components
- Performance benchmarks and scalability
- Python/C++ integration patterns
- Docker and reproducibility framework

**Audience**: HPC researchers, computational physicists, and anyone interested in GPU-accelerated quantum simulations

---

## 🔗 Quick Links

- **Installation**: See [MANUAL.md#installation](MANUAL.md#installation)
- **Quick Start**: See [MANUAL.md#quick-start](MANUAL.md#quick-start)
- **Theory**: See [BSD_FRAMEWORK.md#core-theoretical-results](BSD_FRAMEWORK.md#core-theoretical-results)
- **Paper References**: See [BSD_FRAMEWORK.md#paper-to-code-mapping](BSD_FRAMEWORK.md#paper-to-code-mapping)

## 📖 Related Documentation

- **[../README.md](../README.md)** - Main repository overview
- **[../USAGE.md](../USAGE.md)** - Quick usage guide
- **[../CONTRIBUTING.md](../CONTRIBUTING.md)** - Contribution guidelines
- **[../examples/demo_notebook.ipynb](../examples/demo_notebook.ipynb)** - Interactive examples

## 💡 Where to Start

1. **New to the project?** Start with the main [README.md](../README.md)
2. **Want to run the code?** Go to [MANUAL.md](MANUAL.md)
3. **Interested in the theory?** Read [BSD_FRAMEWORK.md](BSD_FRAMEWORK.md)
4. **Want to contribute?** Check [CONTRIBUTING.md](../CONTRIBUTING.md)

## 🎯 Documentation Goals

This documentation aims to:

- ✅ Provide clear installation and usage instructions
- ✅ Establish direct paper-to-code traceability
- ✅ Explain the theoretical foundations rigorously
- ✅ Enable independent verification of results
- ✅ Support community contributions

## 📝 Documentation Standards

All documentation follows these principles:

- **Clarity**: Written for both mathematicians and programmers
- **Completeness**: Covers installation, usage, and theory
- **Reproducibility**: All examples can be reproduced
- **Traceability**: Direct links between theory and implementation
- **Honesty**: Clear about what is proved and what is pending

## 🔄 Updates

Documentation is updated with each release. See [../CHANGELOG.md](../CHANGELOG.md) for version history.

**Current version**: 0.2.0 (Pending)  
**Last updated**: January 2025

---

For questions or suggestions about the documentation, please open an issue on GitHub.
