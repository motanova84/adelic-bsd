# Codecov Setup Guide

## Installing the Codecov GitHub App

To ensure reliable processing of Codecov uploads and PR comments, the Codecov GitHub App must be installed for this repository.

### Installation Steps

1. **Install the Codecov GitHub App**
   - Visit: https://github.com/apps/codecov
   - Click "Install" or "Configure"
   - Select the `motanova84` account or organization
   - Choose "Only select repositories" and select `adelic-bsd`
   - Click "Install" or "Save"

2. **Verify Installation**
   - Visit: https://app.codecov.io/gh/motanova84/adelic-bsd
   - You should see the repository listed and synced
   - The app provides tokenless authentication for GitHub Actions

### Benefits of the GitHub App

The Codecov GitHub App provides several advantages over token-based uploads:

- **Tokenless Authentication**: No need to manage `CODECOV_TOKEN` secrets
- **Reliable Uploads**: Better handling of upload retries and failures
- **Enhanced PR Comments**: More detailed and reliable PR comments with coverage reports
- **Status Checks**: Automatic status checks on pull requests
- **Better Security**: App-based authentication is more secure than tokens

### Current Configuration

The repository is configured with:

1. **codecov.yml**: Configuration file with coverage settings, comment behavior, and ignore patterns
2. **GitHub Actions Workflows**: Multiple workflows upload coverage:
   - `ci-safe-tests.yml`: Unit tests coverage
   - `python-tests.yml`: Python package tests
   - `operator-proof-validation.yml`: Operator proof validation coverage
   - `crypto-validation.yml`: Cryptographic validation coverage

### Migration from Token to App

If the Codecov GitHub App is installed, the workflows can optionally remove the `token: ${{ secrets.CODECOV_TOKEN }}` parameter. However, keeping it provides backward compatibility and doesn't cause issues when the app is also installed.

The app will automatically authenticate using the GitHub Actions OIDC token when available, falling back to the explicit token if needed.

### Verification

After installing the app, verify it's working by:

1. Push a change or trigger a workflow
2. Check the workflow run logs for successful Codecov uploads
3. Visit https://app.codecov.io/gh/motanova84/adelic-bsd to see updated coverage
4. Verify PR comments appear on new pull requests with coverage information

### Troubleshooting

If uploads fail after app installation:

1. Verify the app has access to the repository in GitHub settings
2. Check that workflows have appropriate permissions (no permission restrictions blocking the app)
3. Review workflow logs for specific error messages
4. Ensure `codecov.yml` is valid and properly formatted

### Documentation

- Codecov GitHub App: https://docs.codecov.com/docs/github-app-integration
- Codecov YAML Reference: https://docs.codecov.com/docs/codecov-yaml
- GitHub Actions Integration: https://docs.codecov.com/docs/github-actions

## Badge and Status

The README includes a Codecov badge that displays current coverage:

```markdown
[![codecov](https://codecov.io/gh/motanova84/adelic-bsd/branch/main/graph/badge.svg)](https://codecov.io/gh/motanova84/adelic-bsd)
```

This badge automatically updates when new coverage data is uploaded.
