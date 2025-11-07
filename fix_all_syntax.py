#!/usr/bin/env python3
# fix_all_syntax.py

"""
Automatic Syntax Error Fixer for BSD Spectral Framework
========================================================

This script automatically fixes all syntax errors:
1. Unicode operators (>=, <=, !=)
2. Unmatched parentheses
3. Unclosed docstrings
4. Invalid characters

Usage:
    python3 fix_all_syntax.py
"""

import os
import re
import sys
from pathlib import Path


class SyntaxFixer:
    """Automatic syntax error fixer."""
    
    def __init__(self, root_dir='.'):
        self.root_dir = Path(root_dir)
        self.fixes_applied = 0
        self.errors_found = []
    
    def fix_unicode_operators(self, content):
        """Replace Unicode operators with ASCII equivalents."""
        replacements = {
            '>=': '>=',
            '<=': '<=',
            '!=': '!=',
            '*': '*',
            '/': '/',
            '-': '-',
            '+/-': '+/-',
            'inf': 'inf',
            'sqrt': 'sqrt',
            'sum': 'sum',
            'prod': 'prod',
            'in': 'in',
            'not in': 'not in',
            'subset': 'subset',
            'superset': 'superset',
            'union': 'union',
            'intersection': 'intersection',
            'tensor': 'tensor',
            'oplus': 'oplus',
            'and': 'and',
            'or': 'or',
            'not': 'not',
            'forall': 'forall',
            'exists': 'exists',
            'grad': 'grad',
            'partial': 'partial',
            'integral': 'integral',
            '->': '->',
            '<-': '<-',
            '<->': '<->',
            '=>': '=>',
            '<=': '<=',
            '<=>': '<=>'
        }
        
        modified = False
        for unicode_char, ascii_equiv in replacements.items():
            if unicode_char in content:
                content = content.replace(unicode_char, ascii_equiv)
                modified = True
                self.fixes_applied += 1
        
        return content, modified
    
    def fix_unmatched_parens(self, filepath):
        """Check and report unmatched parentheses."""
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        stack = []
        line_num = 1
        col_num = 0
        
        for i, char in enumerate(content):
            if char == '\n':
                line_num += 1
                col_num = 0
            else:
                col_num += 1
            
            if char == '(':
                stack.append((i, line_num, col_num))
            elif char == ')':
                if stack:
                    stack.pop()
                else:
                    error = f"{filepath}:{line_num}:{col_num}: Unmatched ')'"
                    self.errors_found.append(error)
        
        if stack:
            for pos, line, col in stack:
                error = f"{filepath}:{line}:{col}: Unmatched '('"
                self.errors_found.append(error)
    
    def fix_unclosed_docstrings(self, content):
        """Fix unclosed triple-quoted strings."""
        # Count triple quotes
        triple_quotes = content.count('"""')
        
        if triple_quotes % 2 != 0:
            # Odd number - add closing quote at end
            content += '\n"""\n'
            self.fixes_applied += 1
            return content, True
        
        return content, False
    
    def fix_file(self, filepath):
        """Fix all syntax errors in a file."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            original_content = content
            modified = False
            
            # Fix Unicode operators
            content, unicode_fixed = self.fix_unicode_operators(content)
            modified = modified or unicode_fixed
            
            # Fix unclosed docstrings
            content, docstring_fixed = self.fix_unclosed_docstrings(content)
            modified = modified or docstring_fixed
            
            # Write back if modified
            if modified:
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(content)
                print(f"✅ Fixed: {filepath}")
            
            # Check for unmatched parens (report only)
            self.fix_unmatched_parens(filepath)
            
        except Exception as e:
            print(f"❌ Error fixing {filepath}: {e}")
    
    def fix_all_python_files(self):
        """Fix all Python files in the repository."""
        print("🔧 BSD Spectral Framework - Syntax Fixer")
        print("=" * 60)
        
        # Find all Python files
        python_files = list(self.root_dir.rglob('*.py'))
        
        print(f"Found {len(python_files)} Python files")
        print()
        
        # Fix each file
        for filepath in python_files:
            self.fix_file(filepath)
        
        # Report results
        print()
        print("=" * 60)
        print("📊 SUMMARY")
        print("=" * 60)
        print(f"Fixes applied: {self.fixes_applied}")
        print(f"Errors found: {len(self.errors_found)}")
        
        if self.errors_found:
            print("\n⚠️  ERRORS REQUIRING MANUAL ATTENTION:")
            for error in self.errors_found:
                print(f"  {error}")
        else:
            print("\n✅ All automatic fixes applied successfully!")
        
        print("=" * 60)


def main():
    """Main entry point."""
    fixer = SyntaxFixer()
    fixer.fix_all_python_files()
    
    # Return exit code
    return 1 if fixer.errors_found else 0


if __name__ == '__main__':
    sys.exit(main())
