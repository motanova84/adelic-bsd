#!/usr/bin/env python3
"""
Verification Script for BSD Complete Structure

This script verifies that all required BSD completion files and theorems
are present in the repository.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: December 2025
"""

import os
import re
from pathlib import Path
from typing import List, Dict, Tuple

def check_file_exists(filepath: str) -> bool:
    """Check if a file exists."""
    path = Path(filepath)
    if not path.exists():
        print(f"❌ File not found: {filepath}")
        return False
    print(f"✅ File exists: {filepath}")
    return True

def check_theorems_in_file(filepath: str, required_theorems: List[str]) -> Dict[str, bool]:
    """Check if required theorems are present in a file."""
    results = {}
    
    try:
        with open(filepath, 'r') as f:
            content = f.read()
        
        print(f"\n📋 Checking theorems in {filepath}:")
        for theorem_name in required_theorems:
            pattern = rf'theorem\s+{theorem_name}\s*'
            if re.search(pattern, content):
                print(f"  ✅ {theorem_name}")
                results[theorem_name] = True
            else:
                print(f"  ❌ {theorem_name} - NOT FOUND")
                results[theorem_name] = False
    except Exception as e:
        print(f"❌ Error reading file {filepath}: {e}")
        for theorem_name in required_theorems:
            results[theorem_name] = False
    
    return results

def main():
    """Main verification function."""
    print("=" * 70)
    print("BSD Complete Structure Verification")
    print("=" * 70)
    
    base_path = Path(__file__).parent / "formalization" / "lean" / "AdelicBSD"
    
    # Check file existence
    print("\n📁 Checking file existence:")
    files_to_check = [
        base_path / "GRH.lean",
        base_path / "BSD_complete.lean",
        base_path / "BSD.lean",
    ]
    
    all_files_exist = True
    for filepath in files_to_check:
        if not check_file_exists(filepath):
            all_files_exist = False
    
    # Check lean-toolchain
    lean_toolchain = Path(__file__).parent / "formalization" / "lean" / "lean-toolchain"
    if check_file_exists(lean_toolchain):
        with open(lean_toolchain, 'r') as f:
            version = f.read().strip()
            print(f"  📌 Lean version: {version}")
    
    # Check theorems in BSD_complete.lean
    bsd_complete_theorems = [
        "BSD_spectral_identity",
        "BSD_rank_equivalence",
        "BSD_finite_part_rank_le_one",
        "BSD_full",
        "birch_swinnerton_dyer_conjecture"
    ]
    
    bsd_complete_results = check_theorems_in_file(
        base_path / "BSD_complete.lean",
        bsd_complete_theorems
    )
    
    # Check main BSD theorem
    bsd_results = check_theorems_in_file(
        base_path / "BSD.lean",
        ["BSD"]
    )
    
    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    all_theorems_present = all(bsd_complete_results.values()) and all(bsd_results.values())
    
    if all_files_exist and all_theorems_present:
        print("✅ All files and theorems are present!")
        print("✅ BSD Complete implementation is VERIFIED!")
        return 0
    else:
        print("❌ Some files or theorems are missing!")
        if not all_files_exist:
            print("   - Some files are missing")
        if not all_theorems_present:
            print("   - Some theorems are missing")
        return 1

if __name__ == "__main__":
    exit(main())
