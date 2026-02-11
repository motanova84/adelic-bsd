# ⚠️ Codecov GitHub App Installation Required

## Action Required

To ensure reliable Codecov upload processing and PR comments, please install the **Codecov GitHub App** for this repository.

## Installation Link

**[Install Codecov GitHub App](https://github.com/apps/codecov)**

## Quick Steps

1. Click the link above or visit: https://github.com/apps/codecov
2. Click "Configure" (if already installed) or "Install" (if new installation)
3. Select the repository owner: **motanova84**
4. Choose **"Only select repositories"**
5. Select **adelic-bsd** from the list
6. Click **"Install"** or **"Save"**

## Verification

After installation, verify the app is working:

1. Push a commit or trigger a workflow
2. Check workflow logs for successful Codecov uploads
3. Visit https://app.codecov.io/gh/motanova84/adelic-bsd
4. Verify coverage data appears
5. Check that PR comments include coverage reports

## Benefits

✅ **Tokenless Authentication** - No need to manage `CODECOV_TOKEN` secrets  
✅ **Reliable Uploads** - Better handling of upload retries and failures  
✅ **Enhanced PR Comments** - More detailed coverage reports in pull requests  
✅ **Status Checks** - Automatic status checks on PRs  
✅ **Better Security** - App-based authentication is more secure than tokens  

## Documentation

Full setup guide: [docs/CODECOV_SETUP.md](../docs/CODECOV_SETUP.md)

## Current Status

- ✅ `codecov.yml` configuration file created and optimized
- ✅ GitHub Actions workflows configured to upload coverage
- ✅ Documentation created in `docs/CODECOV_SETUP.md`
- ⚠️ **GitHub App installation pending** (manual action required by repository owner)

## Configuration Changes Made

The following files have been configured for Codecov GitHub App integration:

1. **codecov.yml**: Updated with GitHub App specific settings
   - Added `github_checks.annotations: true` for PR file annotations
   - Added `show_carryforward_flags: true` for better visibility
   - Optimized comment settings for PR integration

2. **docs/CODECOV_SETUP.md**: Complete setup and troubleshooting guide

3. **README.md**: Added Codecov App reference and documentation link

4. **CONTRIBUTING.md**: Updated with Codecov setup guide reference

## Notes

- The existing `CODECOV_TOKEN` in GitHub Secrets can remain as a fallback
- The app will use tokenless authentication when available
- All workflows are already configured to work with the app
- No code changes are required after app installation

---

**This file can be deleted after the Codecov GitHub App has been successfully installed and verified.**
