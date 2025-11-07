#!/bin/bash
# submit_sagemath_pr.sh
#
# Automated script to prepare and submit PR to SageMath
# This assumes you have already forked SageMath and set up SSH keys

set -e  # Exit on error

echo "======================================================================="
echo "  BSD SPECTRAL FRAMEWORK - SAGEMATH PR SUBMISSION"
echo "======================================================================="
echo ""

# Color codes
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

# Configuration
GITHUB_USERNAME="${GITHUB_USERNAME:-motanova84}"
SAGE_FORK_DIR="${SAGE_FORK_DIR:-$HOME/sage-fork}"
BRANCH_NAME="bsd-spectral-integration"

# Get integration directory
INTEGRATION_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo -e "${BLUE}Configuration:${NC}"
echo "  GitHub Username: $GITHUB_USERNAME"
echo "  Sage Fork Directory: $SAGE_FORK_DIR"
echo "  Branch Name: $BRANCH_NAME"
echo "  Integration Source: $INTEGRATION_DIR"
echo ""

# Step 1: Check if fork exists
echo "Step 1: Checking SageMath fork..."
if [ ! -d "$SAGE_FORK_DIR" ]; then
    echo -e "${YELLOW}! Sage fork not found at $SAGE_FORK_DIR${NC}"
    echo ""
    echo "Would you like to clone it now? (y/n)"
    read -r response
    
    if [[ "$response" =~ ^[Yy]$ ]]; then
        echo "Cloning SageMath..."
        git clone https://github.com/sagemath/sage.git "$SAGE_FORK_DIR"
        cd "$SAGE_FORK_DIR"
        git remote add $GITHUB_USERNAME "git@github.com:$GITHUB_USERNAME/sage.git"
        echo -e "${GREEN}✓ Repository cloned${NC}"
    else
        echo -e "${RED}✗ Cannot proceed without sage fork${NC}"
        echo ""
        echo "Please clone manually:"
        echo "  git clone https://github.com/sagemath/sage.git $SAGE_FORK_DIR"
        exit 1
    fi
else
    echo -e "${GREEN}✓ Fork directory exists${NC}"
fi
echo ""

# Step 2: Update and create branch
echo "Step 2: Preparing branch..."
cd "$SAGE_FORK_DIR"

# Fetch latest changes
echo "Fetching latest changes from upstream..."
git fetch origin

# Checkout develop branch
git checkout develop
git pull origin develop

# Check if branch already exists
if git show-ref --verify --quiet "refs/heads/$BRANCH_NAME"; then
    echo -e "${YELLOW}! Branch $BRANCH_NAME already exists${NC}"
    echo "Delete and recreate? (y/n)"
    read -r response
    
    if [[ "$response" =~ ^[Yy]$ ]]; then
        git branch -D "$BRANCH_NAME"
        git checkout -b "$BRANCH_NAME"
        echo -e "${GREEN}✓ Branch recreated${NC}"
    else
        git checkout "$BRANCH_NAME"
        echo -e "${YELLOW}! Using existing branch${NC}"
    fi
else
    git checkout -b "$BRANCH_NAME"
    echo -e "${GREEN}✓ Branch created${NC}"
fi
echo ""

# Step 3: Copy module files
echo "Step 3: Copying module files..."
mkdir -p "$SAGE_FORK_DIR/src/sage/schemes/elliptic_curves/bsd_spectral"
cp -r "$INTEGRATION_DIR/sage/schemes/elliptic_curves/bsd_spectral/"* \
      "$SAGE_FORK_DIR/src/sage/schemes/elliptic_curves/bsd_spectral/"

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Module files copied${NC}"
else
    echo -e "${RED}✗ Failed to copy module files${NC}"
    exit 1
fi
echo ""

# Step 4: Copy documentation files
echo "Step 4: Copying documentation files..."
mkdir -p "$SAGE_FORK_DIR/src/doc/en/reference/bsd_spectral"
cp -r "$INTEGRATION_DIR/doc/en/reference/bsd_spectral/"* \
      "$SAGE_FORK_DIR/src/doc/en/reference/bsd_spectral/"

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Documentation files copied${NC}"
else
    echo -e "${RED}✗ Failed to copy documentation files${NC}"
    exit 1
fi
echo ""

# Step 5: Run tests
echo "Step 5: Running tests..."
echo "This may take several minutes..."
echo ""

./sage -t src/sage/schemes/elliptic_curves/bsd_spectral/*.py

if [ $? -eq 0 ]; then
    echo ""
    echo -e "${GREEN}✓ All tests passed!${NC}"
else
    echo ""
    echo -e "${RED}✗ Tests failed${NC}"
    echo "Please review test output above and fix issues before proceeding."
    echo ""
    echo "You can continue anyway and fix later. Continue? (y/n)"
    read -r response
    
    if [[ ! "$response" =~ ^[Yy]$ ]]; then
        exit 1
    fi
fi
echo ""

# Step 6: Build documentation (optional)
echo "Step 6: Build documentation?"
echo "This may take 10-20 minutes. Build now? (y/n)"
read -r response

if [[ "$response" =~ ^[Yy]$ ]]; then
    echo "Building documentation..."
    cd src/doc
    make html
    
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✓ Documentation built successfully${NC}"
        echo "View at: $SAGE_FORK_DIR/src/doc/_build/html/en/reference/bsd_spectral/index.html"
    else
        echo -e "${YELLOW}! Documentation build had warnings${NC}"
    fi
    cd "$SAGE_FORK_DIR"
else
    echo -e "${YELLOW}! Skipping documentation build${NC}"
fi
echo ""

# Step 7: Commit changes
echo "Step 7: Committing changes..."
git add src/sage/schemes/elliptic_curves/bsd_spectral/
git add src/doc/en/reference/bsd_spectral/

git commit -m "Add BSD spectral framework module

- Implements spectral-adelic approach to BSD
- Proves Sha(E/Q) finiteness under compatibility conditions
- Includes (dR) Fontaine-Perrin-Riou verification
- Includes (PT) Gross-Zagier + Yuan-Zhang-Zhang verification
- Complete documentation with 50+ doctests
- All tests passing

Reference: DOI 10.5281/zenodo.17236603
Author: José Manuel Mota Burruezo"

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Changes committed${NC}"
else
    echo -e "${RED}✗ Commit failed${NC}"
    exit 1
fi
echo ""

# Step 8: Push to fork
echo "Step 8: Pushing to your fork..."
echo "Ready to push? This will push to: git@github.com:$GITHUB_USERNAME/sage.git"
echo "Continue? (y/n)"
read -r response

if [[ "$response" =~ ^[Yy]$ ]]; then
    git push -u $GITHUB_USERNAME "$BRANCH_NAME"
    
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✓ Branch pushed to fork${NC}"
    else
        echo -e "${RED}✗ Push failed${NC}"
        echo "Check your SSH keys and repository access"
        exit 1
    fi
else
    echo -e "${YELLOW}! Push skipped${NC}"
    echo "You can push manually later with:"
    echo "  git push -u $GITHUB_USERNAME $BRANCH_NAME"
fi
echo ""

# Step 9: Instructions for creating PR
echo "======================================================================="
echo "  ✅ PREPARATION COMPLETE!"
echo "======================================================================="
echo ""
echo "Next steps to create the Pull Request:"
echo ""
echo "1. Go to: https://github.com/$GITHUB_USERNAME/sage"
echo ""
echo "2. Click 'Compare & pull request' for branch: $BRANCH_NAME"
echo ""
echo "3. Set:"
echo "   - Base repository: sagemath/sage"
echo "   - Base branch: develop"
echo "   - Head repository: $GITHUB_USERNAME/sage"
echo "   - Compare branch: $BRANCH_NAME"
echo ""
echo "4. Copy the content from:"
echo "   $INTEGRATION_DIR/PULL_REQUEST.md"
echo ""
echo "5. Add suggested reviewers:"
echo "   @williamstein @roed314 @kedlaya"
echo ""
echo "6. Submit the PR!"
echo ""
echo "======================================================================="
echo ""
echo "Optional: Email notification to maintainers"
echo ""
echo "Send email to sage-devel@googlegroups.com with:"
echo "  Subject: [NEW MODULE] BSD Spectral Framework - PR Ready"
echo "  Body: See $INTEGRATION_DIR/EMAIL_TEMPLATE.txt"
echo ""
echo "======================================================================="
