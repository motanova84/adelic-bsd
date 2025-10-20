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
        """Specifically verify the Theorem 8.3 formula uses escaped \\#"""
        # Find Theorem 8.3 section - need to capture BOTH formulas
        # First formula: order of vanishing formula
        # Second formula: BSD leading term formula (the one with \# characters)
        theorem_pattern = r'\*\*\[Theorem 8\.3\]\*\*.*?\$\$(.*?)\$\$.*?\$\$(.*?)\$\$'
        match = re.search(theorem_pattern, self.content, re.DOTALL)

        self.assertIsNotNone(match, "Theorem 8.3 formulas not found in README")

        # The BSD formula is the second one (group 2)
        formula = match.group(2)

        # Verify escaped # is present
        escaped_hashes = re.findall(r'\\#', formula)
        self.assertGreater(len(escaped_hashes), 0,
                           "Theorem 8.3 BSD formula should contain escaped \\# characters")

        # Verify no unescaped # is present
        unescaped_hashes = re.findall(r'(?<!\\)#', formula)
        self.assertEqual(len(unescaped_hashes), 0,
                         f"Theorem 8.3 BSD formula contains {len(unescaped_hashes)} unescaped # character(s)")

        print(f"✅ Theorem 8.3 BSD formula correctly uses {len(escaped_hashes)} escaped \\# character(s)")

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
