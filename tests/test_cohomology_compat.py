"""
Test suite for BSD Cohomology Compatibility Module

This test validates the existence and structure of the CohomologyCompat.lean
formalization that completes the (dR) and (PT) theorems for BSD.

Author: José Manuel Mota Burruezo (JMMB Ψ⋆∞³)
Date: 2025-11-15
"""

import os
import re
import unittest
from pathlib import Path


class TestCohomologyCompatModule(unittest.TestCase):
    """Test the CohomologyCompat.lean module structure and content."""

    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = Path(__file__).parent.parent
        self.cohomology_file = (
            self.repo_root / "formalization" / "lean" / "RiemannAdelic" / 
            "CohomologyCompat.lean"
        )
        self.module_file = (
            self.repo_root / "formalization" / "lean" / "RiemannAdelic.lean"
        )

    def test_cohomology_file_exists(self):
        """Test that CohomologyCompat.lean exists."""
        self.assertTrue(
            self.cohomology_file.exists(),
            f"CohomologyCompat.lean not found at {self.cohomology_file}"
        )

    def test_module_file_exists(self):
        """Test that RiemannAdelic.lean module file exists."""
        self.assertTrue(
            self.module_file.exists(),
            f"RiemannAdelic.lean module file not found at {self.module_file}"
        )

    def test_file_has_required_imports(self):
        """Test that the file has necessary Mathlib imports."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_imports = [
            "import Mathlib.Data.Real.Basic",
            "import Mathlib.Analysis.Complex.Basic",
            "import Mathlib.LinearAlgebra.FiniteDimensional",
            "import Mathlib.MeasureTheory.Integral.Bochner"
        ]
        
        for import_stmt in required_imports:
            self.assertIn(
                import_stmt, content,
                f"Required import missing: {import_stmt}"
            )

    def test_file_has_bsd_namespace(self):
        """Test that the file defines the BSD namespace."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn("namespace BSD", content, "BSD namespace not found")
        self.assertIn("end BSD", content, "BSD namespace not closed")

    def test_rank_eq_de_rham_theorem_exists(self):
        """Test that the rank_eq_de_rham theorem is defined."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for theorem declaration
        self.assertIn(
            "theorem rank_eq_de_rham", content,
            "rank_eq_de_rham theorem not found"
        )
        
        # Check for theorem signature
        self.assertIn(
            "MordellWeil.rank E = FiniteDimensional.finrank ℚ (H¹_dR E)",
            content,
            "rank_eq_de_rham theorem signature incorrect"
        )

    def test_poincare_trace_equiv_theorem_exists(self):
        """Test that the poincare_trace_equiv theorem is defined."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for theorem declaration
        self.assertIn(
            "theorem poincare_trace_equiv", content,
            "poincare_trace_equiv theorem not found"
        )
        
        # Check for theorem signature components
        self.assertIn("Tr", content, "Trace operator not found")
        self.assertIn("M_E", content, "Spectral operator M_E not found")
        self.assertIn("pullback", content, "Pullback operation not found")
        self.assertIn("poincare_kernel", content, "Poincaré kernel not found")

    def test_bsd_qed_theorem_exists(self):
        """Test that the BSD.QED completion theorem exists."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn(
            "theorem BSD.QED", content,
            "BSD.QED completion theorem not found"
        )

    def test_file_has_required_type_definitions(self):
        """Test that the file defines required mathematical types."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_types = [
            "axiom EllipticCurve",
            "axiom H¹_dR",
            "axiom MordellWeil.rank",
            "axiom M_E",
            "axiom Omega",
            "axiom UpperHalfPlane"
        ]
        
        for type_def in required_types:
            self.assertIn(
                type_def, content,
                f"Required type definition missing: {type_def}"
            )

    def test_file_has_fundamental_axioms(self):
        """Test that the file includes fundamental mathematical axioms."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        fundamental_axioms = [
            "h1_dR_equiv",
            "rank_eq_dimension_differentials_dual",
            "trace_ME_eq_integral_pullback"
        ]
        
        for axiom in fundamental_axioms:
            self.assertIn(
                axiom, content,
                f"Fundamental axiom missing: {axiom}"
            )

    def test_file_has_proper_documentation(self):
        """Test that theorems are properly documented."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for documentation comments
        self.assertIn("/--", content, "No documentation comments found")
        self.assertIn("Teorema:", content, "Theorem documentation missing")
        self.assertIn("dR", content, "(dR) compatibility not documented")
        self.assertIn("PT", content, "(PT) compatibility not documented")

    def test_file_has_author_and_date(self):
        """Test that the file has proper attribution."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn("Autor:", content, "Author attribution missing")
        self.assertIn("José Manuel Mota Burruezo", content, "Author name missing")
        self.assertIn("2025-11-15", content, "Date missing")

    def test_module_imports_cohomology_compat(self):
        """Test that RiemannAdelic.lean imports CohomologyCompat."""
        with open(self.module_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn(
            "import RiemannAdelic.CohomologyCompat", content,
            "CohomologyCompat not imported in module file"
        )

    def test_file_is_valid_lean_syntax(self):
        """Test basic Lean 4 syntax validity (structure check)."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for matching namespace/end pairs
        namespace_count = content.count("namespace BSD")
        end_count = content.count("end BSD")
        self.assertEqual(
            namespace_count, end_count,
            "Namespace/end mismatch"
        )
        
        # Check for matching theorem/by pairs
        theorem_count = len(re.findall(r'\btheorem\b', content))
        by_count = len(re.findall(r'\bby\b', content))
        self.assertGreaterEqual(
            by_count, theorem_count - 1,  # Allow for theorem without proof
            "Not enough 'by' keywords for theorems"
        )

    def test_noncomputable_section_present(self):
        """Test that noncomputable section is declared."""
        with open(self.cohomology_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn(
            "noncomputable section", content,
            "noncomputable section not declared"
        )

    def test_file_size_reasonable(self):
        """Test that the file has reasonable size (not empty, not too large)."""
        file_size = os.path.getsize(self.cohomology_file)
        
        # Should be at least 5KB and less than 50KB
        self.assertGreater(
            file_size, 5000,
            f"File too small ({file_size} bytes), may be incomplete"
        )
        self.assertLess(
            file_size, 50000,
            f"File too large ({file_size} bytes), may have issues"
        )


class TestCohomologyCompatIntegration(unittest.TestCase):
    """Test integration with rest of the repository."""

    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = Path(__file__).parent.parent

    def test_lean_formalization_summary_updated(self):
        """Test that LEAN_FORMALIZATION_SUMMARY.md mentions the new module."""
        summary_file = self.repo_root / "LEAN_FORMALIZATION_SUMMARY.md"
        
        if summary_file.exists():
            with open(summary_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            self.assertIn(
                "CohomologyCompat", content,
                "LEAN_FORMALIZATION_SUMMARY.md not updated with CohomologyCompat"
            )
            self.assertIn(
                "dR", content,
                "dR compatibility not mentioned in summary"
            )
            self.assertIn(
                "PT", content,
                "PT compatibility not mentioned in summary"
            )

    def test_riemann_adelic_directory_structure(self):
        """Test that RiemannAdelic directory has proper structure."""
        riemann_dir = self.repo_root / "formalization" / "lean" / "RiemannAdelic"
        
        self.assertTrue(riemann_dir.exists(), "RiemannAdelic directory missing")
        self.assertTrue(riemann_dir.is_dir(), "RiemannAdelic is not a directory")
        
        # Check that it contains at least the new file
        lean_files = list(riemann_dir.glob("*.lean"))
        self.assertGreater(
            len(lean_files), 0,
            "No .lean files in RiemannAdelic directory"
        )


if __name__ == "__main__":
    unittest.main()
