# 🚀 SageMath PR Quick Start Guide

This guide will help you submit the BSD Spectral Framework to the SageMath repository.

---

## ⚡ TL;DR - Fast Track

```bash
# 1. Verify everything is ready (takes ~30 seconds)
./scripts/final_verification.sh

# 2. Prepare the SageMath PR (interactive, takes ~5 minutes)
./scripts/prepare_sagemath_pr.sh

# 3. Push and create PR (follow instructions from step 2)
```

---

## 📋 Prerequisites

- [x] All tests passing (verified by `final_verification.sh`)
- [x] GitHub account with fork of sagemath/sage
- [x] Git configured with your credentials
- [ ] SageMath repository cloned (the script can help with this)

---

## 🎯 Step-by-Step Process

### Step 1: Verify Project Status

Run the final verification script to ensure everything is ready:

```bash
./scripts/final_verification.sh
```

**Expected output:**
```
╔═══════════════════════════════════════════════════════════╗
║          🎉 ALL CRITICAL CHECKS PASSED! 🎉                ║
║              READY FOR SAGEMATH PR                        ║
╚═══════════════════════════════════════════════════════════╝
```

**If you see this:** ✅ Proceed to Step 2  
**If you see errors:** ❌ Fix the issues reported, then try again

---

### Step 2: Prepare SageMath PR

Run the preparation script:

```bash
./scripts/prepare_sagemath_pr.sh
```

**What this does:**
1. Checks if you have SageMath cloned (offers to guide you if not)
2. Creates a new branch `bsd-spectral-framework`
3. Copies all necessary files to SageMath structure
4. Creates a comprehensive commit message
5. Provides next steps

**Interactive prompts you'll see:**
- Location of SageMath fork (default: `../sagemath-fork`)
- Whether to recreate branch if it exists
- Whether to run SageMath tests now

**What to answer:**
- Accept defaults if this is your first time
- Say "yes" to running tests if you have time (~5 minutes)

---

### Step 3: Push to Your Fork

Follow the instructions printed by the script. Typically:

```bash
# Navigate to SageMath directory
cd ../sagemath-fork  # or wherever your fork is

# Push to your fork
git push -u YOUR_USERNAME bsd-spectral-framework
```

Replace `YOUR_USERNAME` with your GitHub username.

**Example:**
```bash
git push -u motanova84 bsd-spectral-framework
```

---

### Step 4: Create Pull Request on GitHub

1. **Go to:** https://github.com/sagemath/sage

2. **Click:** "New Pull Request" (or you'll see a banner suggesting your branch)

3. **Select branches:**
   - Base: `sagemath:develop`
   - Compare: `YOUR_USERNAME:bsd-spectral-framework`

4. **Fill in PR details:**
   - **Title:** `Add BSD Spectral Framework module`
   - **Description:** Copy from `SAGEMATH_PR.md` (it's a ready-to-use template)

5. **Submit:** Click "Create pull request"

---

## 📝 PR Template Location

The complete PR description template is in: **`SAGEMATH_PR.md`**

This file contains:
- Full description of the mathematical framework
- Feature list
- Implementation details
- Validation results
- References

Just copy-paste its contents into the GitHub PR description field.

---

## ⚠️ Troubleshooting

### "SageMath not found"

**Option A - Let the script guide you:**
The script will provide instructions for cloning SageMath.

**Option B - Manual setup:**
```bash
# Clone SageMath
git clone https://github.com/sagemath/sage.git ../sagemath-fork
cd ../sagemath-fork

# Add your fork as remote
git remote add YOUR_USERNAME git@github.com:YOUR_USERNAME/sage.git

# Return to adelic-bsd
cd -

# Run the script again
./scripts/prepare_sagemath_pr.sh
```

### "Branch already exists"

The script will ask if you want to delete and recreate it. Say "yes" if you want a fresh start.

### "Tests failing"

If local tests fail:
1. Check the error message
2. Ensure all dependencies are installed: `pip install -r requirements_ci.txt`
3. Try running individual test files to isolate the issue

If SageMath tests fail:
1. Make sure SageMath is properly built
2. Check the test output for specific errors
3. These errors are often environment-specific and may not block the PR

### "Can't push to fork"

Make sure you've:
1. Created a fork of sagemath/sage on GitHub
2. Added it as a remote: `git remote add YOUR_USERNAME git@github.com:YOUR_USERNAME/sage.git`
3. Set up SSH keys or use HTTPS with credentials

---

## 🎓 What Happens Next?

After you create the PR:

1. **SageMath maintainers will review** your submission
   - They'll check code quality
   - They'll verify mathematical correctness
   - They'll run their own tests

2. **You may receive feedback**
   - Address any comments
   - Make requested changes
   - Push updates to the same branch

3. **PR gets merged** 🎉
   - Your contribution becomes part of SageMath
   - It will be in the next release
   - You're officially a SageMath contributor!

---

## 📊 What Gets Submitted?

The PR includes:

### Code Modules
- `src/sage/schemes/elliptic_curves/bsd_spectral/`
  - Spectral finiteness prover
  - (dR) compatibility verification
  - (PT) compatibility verification
  - Certificate generation

### Documentation
- `src/doc/en/reference/bsd_spectral/`
  - User guide
  - API documentation
  - Mathematical background
  - Examples

### Tests
- `src/sage/tests/elliptic_curves/`
  - Unit tests
  - Integration tests
  - Doctests

### Features
- ✅ No new dependencies
- ✅ 100% backward compatible
- ✅ 150+ doctests
- ✅ Production-ready
- ✅ Fully documented

---

## 🔗 Useful Resources

- **Project README:** `README.md`
- **Complete Status:** `FINAL_STATUS.md`
- **User Guide:** `BSD_SPECTRAL_USER_GUIDE.md`
- **PR Template:** `SAGEMATH_PR.md`
- **Scripts Documentation:** `scripts/README.md`

---

## 💡 Tips

1. **Run verification frequently** during development
   ```bash
   ./scripts/final_verification.sh
   ```

2. **Keep your SageMath fork updated**
   ```bash
   cd ../sagemath-fork
   git fetch origin
   git checkout develop
   git pull origin develop
   ```

3. **Test locally before PR**
   The prepare script offers to run tests - say yes!

4. **Be responsive to feedback**
   SageMath maintainers are helpful but thorough

5. **Celebrate!** 🎉
   Contributing to SageMath is a big achievement

---

## 📞 Getting Help

- **Script issues:** Check `scripts/README.md`
- **Test failures:** Check `FINAL_STATUS.md` for known issues
- **SageMath questions:** Check SageMath documentation or ask in their dev channels
- **Mathematical questions:** See references in `SAGEMATH_PR.md`

---

## ✅ Checklist

Before creating the PR, ensure:

- [ ] `./scripts/final_verification.sh` passes ✅
- [ ] SageMath fork exists and is updated
- [ ] Branch `bsd-spectral-framework` is ready
- [ ] All files copied to SageMath structure
- [ ] Commit message is comprehensive
- [ ] Pushed to your fork
- [ ] Ready to create PR with template from `SAGEMATH_PR.md`

---

**Good luck with your SageMath contribution! 🚀**

*"De lo espectral surge lo aritmético"*

**JMMB Ψ·∴ | 2025**
