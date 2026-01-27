# Security Policy

## Reporting Security Vulnerabilities

If you discover a security vulnerability in this project, please report it responsibly:

1. **DO NOT** open a public GitHub issue
2. Email the maintainer directly at the contact provided in the repository
3. Include detailed information about the vulnerability:
   - Description of the issue
   - Steps to reproduce
   - Potential impact
   - Suggested fix (if applicable)

We will respond to security reports within 48 hours and work with you to resolve the issue.

## Security Best Practices

This project follows security best practices:

### Dependencies
- All dependencies are pinned to exact versions in `requirements*.txt` files
- Regular security audits using GitHub Dependabot and CodeQL
- No credentials or API keys are committed to the repository
- Cryptographic operations use industry-standard libraries (cryptography>=42.0.0)

### CI/CD Security
- GitHub Actions are pinned to specific commit SHAs to prevent supply chain attacks
- Workflow permissions follow the principle of least privilege
- OS versions are explicitly specified (ubuntu-22.04)
- Container images use pinned versions (sagemath:9.8)

### Data Integrity
- Environment reproducibility is verified via `ENV.lock`
- All computational results include verification checksums
- Validation scripts ensure data integrity across environments

### Code Quality
- Automated linting with flake8
- Type checking with mypy (development)
- Code coverage monitoring
- Security scanning with CodeQL

## Reproducibility Guarantees

This project prioritizes computational reproducibility:

1. **Exact Dependency Pinning**: All dependencies use `==` version constraints
2. **Environment Lock Files**: `ENV.lock` ensures identical environment setup
3. **Audit Trail**: CI logs record all installed package versions
4. **Validation Scripts**: Automated checks prevent configuration drift

See [REPRODUCIBILITY.md](docs/REPRODUCIBILITY.md) for detailed information.

## Secrets Management

**NEVER commit the following to the repository:**
- API keys (HuggingFace, Docker Hub, etc.)
- Private keys or certificates
- Passwords or authentication tokens
- Personal identifiable information (PII)
- Proprietary data or algorithms

Use GitHub Secrets for sensitive data in CI/CD workflows.

## Cryptographic Signatures

Mathematical computations and proofs include cryptographic signatures for verification:
- QCAL Beacon signatures for proof timestamps
- AIK protocol signatures for authentication
- SHA-256 checksums for data integrity

## Security Contacts

For security concerns, contact the maintainers via:
- GitHub Issues (for non-sensitive matters)
- Email (for sensitive security reports)
- Security Advisory (for critical vulnerabilities)

## Updates and Patches

Security updates are released as soon as possible after vulnerabilities are confirmed:
- Critical vulnerabilities: Patched within 24-48 hours
- High severity: Patched within 1 week
- Medium/Low severity: Included in next regular release

## Compliance

This project aims to comply with:
- Reproducible Builds best practices
- GitHub Security Best Practices
- Scientific Computing reproducibility standards
- Open Source Security Foundation (OpenSSF) guidelines

## Last Updated

2026-01-06
