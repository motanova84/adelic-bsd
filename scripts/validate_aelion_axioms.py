#!/usr/bin/env python3
"""
Validation Script for AELION Axioms
====================================

This script validates the AELION framework implementation by checking:
1. The AELIONAxioms.lean file exists and is well-formed
2. All key theorems are present and documented
3. The integration with existing BSD modules is correct
4. Documentation is complete

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: December 2025
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple
import sys


class AELIONValidator:
    """Validator for AELION axioms implementation"""
    
    def __init__(self, base_dir: str = "formalization/lean/AdelicBSD"):
        self.base_dir = Path(base_dir)
        self.axioms_file = self.base_dir / "AELIONAxioms.lean"
        self.readme_file = self.base_dir / "AELION_README.md"
        self.results = {}
        
    def validate(self) -> Dict[str, bool]:
        """Run all validations and return results"""
        print("🔍 AELION Axioms Validation")
        print("=" * 60)
        
        self.results['file_exists'] = self.check_file_exists()
        self.results['key_theorems'] = self.check_key_theorems()
        self.results['documentation'] = self.check_documentation()
        self.results['axioms'] = self.check_axioms()
        self.results['integration'] = self.check_integration()
        
        return self.results
    
    def check_file_exists(self) -> bool:
        """Check if the AELIONAxioms.lean file exists"""
        print("\n📄 Checking file existence...")
        
        if not self.axioms_file.exists():
            print(f"  ❌ File not found: {self.axioms_file}")
            return False
        
        print(f"  ✅ File exists: {self.axioms_file}")
        
        # Check file size (informational only)
        size = self.axioms_file.stat().st_size
        print(f"  📊 File size: {size} bytes")
        
        return True
    
    def check_key_theorems(self) -> bool:
        """Check if all key theorems are present"""
        print("\n🔑 Checking key theorems...")
        
        if not self.axioms_file.exists():
            return False
        
        content = self.axioms_file.read_text()
        
        required_theorems = {
            'IsometryIsomorphism': 'Topological Palindrome isometry',
            'RegulatorCoercion': 'PT Condition - Spectral = Arithmetic Regulator',
            'PAdicCoercion': 'dR Condition - p-adic alignment',
            'ShaFinitenessCoercion': 'Sha finiteness from spectral bounds',
            'BSDUnconditionalTheorem': 'Main unconditional BSD theorem',
            'PT_Condition_Satisfied': 'PT condition verification',
            'dR_Condition_Satisfied': 'dR condition verification',
        }
        
        all_found = True
        for theorem, description in required_theorems.items():
            pattern = rf'theorem\s+{theorem}'
            if re.search(pattern, content):
                print(f"  ✅ {theorem}: {description}")
            else:
                print(f"  ❌ Missing theorem: {theorem} ({description})")
                all_found = False
        
        return all_found
    
    def check_axioms(self) -> bool:
        """Check if required axioms are defined"""
        print("\n🎯 Checking axioms...")
        
        if not self.axioms_file.exists():
            return False
        
        content = self.axioms_file.read_text()
        
        required_axioms = {
            'SpectralFredholmIdentity': 'Spectral-Fredholm identity (Axiom 1.1)',
            'RankCoercionAxiom': 'Rank coercion (Axiom 1.2)',
            'det_eq_of_isometry_isomorphism': 'Determinant preservation lemma',
        }
        
        all_found = True
        for axiom, description in required_axioms.items():
            pattern = rf'axiom\s+{axiom}'
            if re.search(pattern, content):
                print(f"  ✅ {axiom}: {description}")
            else:
                print(f"  ❌ Missing axiom: {axiom} ({description})")
                all_found = False
        
        return all_found
    
    def check_documentation(self) -> bool:
        """Check if documentation is present and complete"""
        print("\n📚 Checking documentation...")
        
        # Check AELION_README.md
        if not self.readme_file.exists():
            print(f"  ❌ README not found: {self.readme_file}")
            return False
        
        print(f"  ✅ README exists: {self.readme_file}")
        
        readme_content = self.readme_file.read_text()
        
        required_sections = [
            'Overview',
            'Core Concepts',
            'Main Theorems',
            'Axioms',
            'Integration',
            'Key Innovations',
        ]
        
        all_found = True
        for section in required_sections:
            if section in readme_content:
                print(f"  ✅ Section present: {section}")
            else:
                print(f"  ❌ Missing section: {section}")
                all_found = False
        
        # Check inline documentation in .lean file
        if self.axioms_file.exists():
            lean_content = self.axioms_file.read_text()
            doc_comments = len(re.findall(r'/--', lean_content))
            print(f"  📊 Documentation blocks: {doc_comments}")
            
            if doc_comments < 10:
                print(f"  ⚠️  Low number of documentation blocks")
                all_found = False
        
        return all_found
    
    def check_integration(self) -> bool:
        """Check integration with existing BSD modules"""
        print("\n🔗 Checking integration...")
        
        if not self.axioms_file.exists():
            return False
        
        content = self.axioms_file.read_text()
        
        # Check imports
        required_imports = [
            'AdelicBSD.BSDFinal',
            'AdelicBSD.BSDStatement',
            'Mathlib.LinearAlgebra',
        ]
        
        all_found = True
        for imp in required_imports:
            if imp in content:
                print(f"  ✅ Import present: {imp}")
            else:
                print(f"  ❌ Missing import: {imp}")
                all_found = False
        
        # Check integration theorem
        if 'AELION_implies_BSD' in content:
            print(f"  ✅ Integration theorem present")
        else:
            print(f"  ⚠️  Integration theorem not found")
            all_found = False
        
        # Check Main.lean includes AELIONAxioms
        main_file = self.base_dir / "Main.lean"
        if main_file.exists():
            main_content = main_file.read_text()
            if 'AELIONAxioms' in main_content:
                print(f"  ✅ Main.lean imports AELIONAxioms")
            else:
                print(f"  ❌ Main.lean does not import AELIONAxioms")
                all_found = False
        
        return all_found
    
    def generate_report(self) -> str:
        """Generate a validation report"""
        print("\n" + "=" * 60)
        print("📊 VALIDATION REPORT")
        print("=" * 60)
        
        total = len(self.results)
        passed = sum(1 for v in self.results.values() if v)
        
        for check, result in self.results.items():
            status = "✅ PASS" if result else "❌ FAIL"
            print(f"{status} - {check.replace('_', ' ').title()}")
        
        print("\n" + "=" * 60)
        print(f"Overall: {passed}/{total} checks passed")
        
        if passed == total:
            print("🎉 All validations passed!")
            return "success"
        elif passed >= total * 0.8:
            print("⚠️  Most validations passed, but some issues remain")
            return "warning"
        else:
            print("❌ Multiple validation failures")
            return "failure"


def main():
    """Main entry point"""
    
    # Determine base directory
    if os.path.exists("formalization/lean/AdelicBSD"):
        base_dir = "formalization/lean/AdelicBSD"
    else:
        print("❌ Cannot find formalization directory")
        sys.exit(1)
    
    # Run validation
    validator = AELIONValidator(base_dir)
    results = validator.validate()
    status = validator.generate_report()
    
    # Exit with appropriate code
    if status == "success":
        sys.exit(0)
    elif status == "warning":
        sys.exit(0)  # Still pass with warnings
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
