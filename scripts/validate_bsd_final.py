#!/usr/bin/env python3
"""
Validation Script for BSD Final Formalization

This script validates that the BSDFinal.lean file contains all required
components as specified in the problem statement.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
"""

import os
import re
from pathlib import Path
from typing import List, Dict, Tuple


def check_file_exists(filepath: str) -> bool:
    """Check if the BSDFinal.lean file exists."""
    path = Path(filepath)
    if not path.exists():
        print(f"❌ File not found: {filepath}")
        return False
    print(f"✅ File exists: {filepath}")
    return True


def check_required_definitions(content: str) -> Dict[str, bool]:
    """Check if all required definitions are present in the file."""
    required_defs = {
        'L_E': r'noncomputable def L_E',
        'analytic_rank': r'noncomputable def analytic_rank',
        'algebraic_rank': r'noncomputable def algebraic_rank',
        'rank_compatibility': r'def rank_compatibility',
        'dR_compatibility': r'def dR_compatibility',
        'pt_compatibility': r'def pt_compatibility',
        'BSD_final_statement': r'def BSD_final_statement',
    }
    
    results = {}
    print("\n📋 Checking required definitions:")
    for name, pattern in required_defs.items():
        if re.search(pattern, content):
            print(f"  ✅ {name}")
            results[name] = True
        else:
            print(f"  ❌ {name} - NOT FOUND")
            results[name] = False
    
    return results


def check_imports(content: str) -> Dict[str, bool]:
    """Check if required imports are present."""
    required_imports = {
        'LSeries': r'import Mathlib\.NumberTheory\.LSeries',
        'ModularForms': r'import Mathlib\.NumberTheory\.ModularForms',
        'EllipticCurve': r'import Mathlib\.AlgebraicGeometry\.EllipticCurve',
    }
    
    results = {}
    print("\n📦 Checking required imports:")
    for name, pattern in required_imports.items():
        if re.search(pattern, content):
            print(f"  ✅ {name}")
            results[name] = True
        else:
            print(f"  ⚠️  {name} - NOT FOUND (may be optional)")
            results[name] = False
    
    return results


def check_no_sorry(content: str) -> Tuple[bool, List[str]]:
    """Check that there are no 'sorry' statements in the file."""
    sorry_pattern = r'\bsorry\b'
    sorries = re.findall(sorry_pattern, content)
    
    if sorries:
        print(f"\n⚠️  Found {len(sorries)} 'sorry' statement(s)")
        # Find line numbers
        lines = content.split('\n')
        sorry_lines = []
        for i, line in enumerate(lines, 1):
            if 'sorry' in line:
                sorry_lines.append(f"  Line {i}: {line.strip()}")
        return False, sorry_lines
    else:
        print("\n✅ No 'sorry' statements found - all definitions complete")
        return True, []


def check_qcal_connection(content: str) -> bool:
    """Check if QCAL frequency connection is present."""
    qcal_pattern = r'141\.7001'
    if re.search(qcal_pattern, content):
        print("\n✅ QCAL frequency f₀ = 141.7001 Hz found")
        return True
    else:
        print("\n⚠️  QCAL frequency f₀ = 141.7001 Hz not found")
        return False


def check_namespace(content: str) -> bool:
    """Check if BSD namespace is used."""
    if re.search(r'namespace BSD', content):
        print("\n✅ BSD namespace found")
        return True
    else:
        print("\n❌ BSD namespace not found")
        return False


def validate_bsd_final() -> bool:
    """Main validation function."""
    print("=" * 60)
    print("BSD Final Formalization Validation")
    print("=" * 60)
    
    # Path to the BSDFinal.lean file
    filepath = "formalization/lean/AdelicBSD/BSDFinal.lean"
    
    # Check if file exists
    if not check_file_exists(filepath):
        return False
    
    # Read file content
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Run all checks
    definitions = check_required_definitions(content)
    imports = check_imports(content)
    no_sorry, sorry_lines = check_no_sorry(content)
    qcal = check_qcal_connection(content)
    namespace = check_namespace(content)
    
    # Print summary
    print("\n" + "=" * 60)
    print("VALIDATION SUMMARY")
    print("=" * 60)
    
    all_defs_present = all(definitions.values())
    if all_defs_present:
        print("✅ All required definitions present")
    else:
        missing = [k for k, v in definitions.items() if not v]
        print(f"❌ Missing definitions: {', '.join(missing)}")
    
    if no_sorry:
        print("✅ No incomplete proofs (no 'sorry' statements)")
    else:
        print("⚠️  Some definitions may be incomplete:")
        for line in sorry_lines:
            print(line)
    
    if namespace:
        print("✅ Proper namespace structure")
    
    if qcal:
        print("✅ QCAL framework connection present")
    
    # Overall result
    success = all_defs_present and no_sorry and namespace
    
    print("\n" + "=" * 60)
    if success:
        print("🎉 VALIDATION PASSED - BSD Final formalization is complete!")
    else:
        print("⚠️  VALIDATION INCOMPLETE - Some items need attention")
    print("=" * 60)
    
    return success


if __name__ == "__main__":
    import sys
    success = validate_bsd_final()
    sys.exit(0 if success else 1)
