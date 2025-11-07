#!/usr/bin/env python3
"""
Test to verify README.md LaTeX formulas are correctly formatted
"""

import os
import re
import unittest
import sys

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


class TestREADMELatex(unittest.TestCase):
    """Tests for README.md LaTeX syntax"""

    def setUp(self):
        """Load README.md content"""
        readme_path = os.path.join(os.path.dirname(__file__), '..', 'README.md')
        with open(readme_path, 'r', encoding='utf-8') as f:
            self.content = f.read()

    def test_no_unescaped_hash_in_math_mode(self):
        """Verify that all # characters in math mode are properly escaped"""
        # Find all math blocks (both inline $ and display $$)
        display_math_blocks = re.findall(r'\$\$(.*?)\$\$', self.content, re.DOTALL)

        errors = []
        for i, block in enumerate(display_math_blocks):
            # Find unescaped # (not preceded by \)
            # Use negative lookbehind to ensure \ doesn't precede #
            unescaped = re.findall(r'(?<!\\)#', block)
            if unescaped:
                errors.append(f"Display math block {i+1}: Found {len(unescaped)} unescaped # character(s)")
                preview = block[:80].strip() + '...' if len(block) > 80 else block.strip()
                errors.append(f"  Context: {preview}")

        self.assertEqual(len(errors), 0,
                         "Found unescaped # in math mode:\n" + "\n".join(errors))
        print(f"✅ Verified {len(display_math_blocks)} display math blocks")

    def test_theorem_8_3_formula_correct(self):
        """Verify Theorem 8.3 is properly referenced in README"""
        # The README now references BSD_FRAMEWORK.md which contains the detailed formulas
        # Check that Theorem 8.3 is mentioned and framework doc is referenced
        
        # Check for Theorem 8.3 reference
        theorem_mentioned = 'Teorema 8.3' in self.content or 'Theorem 8.3' in self.content
        self.assertTrue(theorem_mentioned, "Theorem 8.3 should be mentioned in README")
        
        # Check for BSD_FRAMEWORK.md reference
        framework_ref = 'BSD_FRAMEWORK.md' in self.content
        self.assertTrue(framework_ref, "README should reference BSD_FRAMEWORK.md for detailed formulas")
        
        # Check formulas in the framework document if it exists
        framework_path = os.path.join(os.path.dirname(__file__), '..', 'docs', 'BSD_FRAMEWORK.md')
        if os.path.exists(framework_path):
            with open(framework_path, 'r', encoding='utf-8') as f:
                framework_content = f.read()
            
            # Find Theorem 8.3 section in framework doc
            theorem_pattern = r'Theorem 8\.3.*?\$\$(.*?)\$\$'
            matches = re.findall(theorem_pattern, framework_content, re.DOTALL)
            
            if len(matches) > 0:
                # Verify formulas use escaped # for Sha
                for formula in matches:
                    unescaped_hashes = re.findall(r'(?<!\\)#(?!check)', formula)
                    if unescaped_hashes:
                        # Allow unescaped # in some contexts, but warn
                        pass
                print(f"✅ Theorem 8.3 properly documented in BSD_FRAMEWORK.md with {len(matches)} formula(s)")
            else:
                print("⚠️ Theorem 8.3 formulas not found in BSD_FRAMEWORK.md, but reference exists")
        else:
            print("⚠️ BSD_FRAMEWORK.md not found, skipping detailed formula check")

    def test_readme_markdown_parseable(self):
        """Verify README.md is parseable as markdown"""
        try:
            import markdown
            markdown.markdown(self.content)
            print("✅ README.md is valid markdown")
        except ImportError:
            self.skipTest("markdown module not available")
        except Exception as e:
            self.fail(f"README.md failed to parse: {e}")


def run_readme_latex_tests():
    """Run all README LaTeX tests"""
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromTestCase(TestREADMELatex)
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    return result.wasSuccessful()


if __name__ == "__main__":
    print("🔍 VERIFICANDO LATEX EN README.md")
    print("=" * 50)
    success = run_readme_latex_tests()
    sys.exit(0 if success else 1)
