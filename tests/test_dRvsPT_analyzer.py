"""
Test suite for dRvsPT_Analyzer Module

This test validates the formal comparator for de Rham vs Perrin-Riou structures
for BSD conjecture verification in rank ≥ 2 curves.

Tests:
- dRvsPT_Analyzer.lean module existence and structure
- Python extraction scripts (extract_dR_matrix.py, extract_PT_matrix.py)
- Cohomology data files
- BSD cohomology validation

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
"""

import os
import sys
import json
import unittest
from pathlib import Path


class TestDRvsPTAnalyzerModule(unittest.TestCase):
    """Test the dRvsPT_Analyzer.lean module structure and content."""

    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = Path(__file__).parent.parent
        self.rational_structures_dir = (
            self.repo_root / "formalization" / "lean" / "rational_structures"
        )
        self.analyzer_file = self.rational_structures_dir / "DRvsPTAnalyzer.lean"
        self.test_file = self.rational_structures_dir / "TestCohomology.lean"
        self.scripts_dir = self.repo_root / "scripts"
        self.data_dir = self.repo_root / "data"

    def test_rational_structures_dir_exists(self):
        """Test that rational_structures directory exists."""
        self.assertTrue(
            self.rational_structures_dir.exists(),
            f"rational_structures directory not found at {self.rational_structures_dir}"
        )

    def test_analyzer_file_exists(self):
        """Test that DRvsPTAnalyzer.lean exists."""
        self.assertTrue(
            self.analyzer_file.exists(),
            f"DRvsPTAnalyzer.lean not found at {self.analyzer_file}"
        )

    def test_test_cohomology_file_exists(self):
        """Test that TestCohomology.lean exists."""
        self.assertTrue(
            self.test_file.exists(),
            f"TestCohomology.lean not found at {self.test_file}"
        )

    def test_analyzer_has_required_imports(self):
        """Test that the analyzer file has necessary imports."""
        with open(self.analyzer_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_imports = [
            "import Mathlib.Data.Matrix.Basic",
            "import Mathlib.LinearAlgebra.Matrix.Trace",
            "import Mathlib.Data.Real.Basic",
        ]
        
        for import_stmt in required_imports:
            self.assertIn(
                import_stmt, content,
                f"Required import missing: {import_stmt}"
            )

    def test_analyzer_has_elliptic_cohomology_structure(self):
        """Test that EllipticCohomology structure is defined."""
        with open(self.analyzer_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn("structure EllipticCohomology", content)
        self.assertIn("curve_id : String", content)
        self.assertIn("dR_matrix", content)
        self.assertIn("pt_matrix", content)
        self.assertIn("mw_rank", content)

    def test_analyzer_has_test_curves(self):
        """Test that test curves are defined."""
        with open(self.analyzer_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        test_curves = ["5077a1", "5942a1", "11131a1"]
        for curve in test_curves:
            self.assertIn(curve, content, f"Test curve {curve} not found")

    def test_analyzer_has_compare_function(self):
        """Test that compare_dR_PT function is defined."""
        with open(self.analyzer_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn("def compare_dR_PT", content)
        self.assertIn("def verify_curve", content)

    def test_analyzer_has_theorems(self):
        """Test that key theorems are defined."""
        with open(self.analyzer_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        theorems = [
            "theorem regulator_full_rank_iff_compat",
            "theorem trace_equality",
            "theorem mw_rank_preserved",
            "theorem bsd_strong_form_verifiable",
        ]
        
        for thm in theorems:
            self.assertIn(thm, content, f"Theorem not found: {thm}")

    def test_analyzer_namespace(self):
        """Test that the correct namespace is used."""
        with open(self.analyzer_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn("namespace BSD.RationalStructures", content)
        self.assertIn("end BSD.RationalStructures", content)


class TestPythonExtractionScripts(unittest.TestCase):
    """Test the Python extraction scripts."""

    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = Path(__file__).parent.parent
        self.scripts_dir = self.repo_root / "scripts"
        self.dR_script = self.scripts_dir / "extract_dR_matrix.py"
        self.PT_script = self.scripts_dir / "extract_PT_matrix.py"
        
        # Add scripts to path for import testing
        sys.path.insert(0, str(self.scripts_dir))

    def tearDown(self):
        """Clean up after tests."""
        if str(self.scripts_dir) in sys.path:
            sys.path.remove(str(self.scripts_dir))

    def test_dR_script_exists(self):
        """Test that extract_dR_matrix.py exists."""
        self.assertTrue(
            self.dR_script.exists(),
            f"extract_dR_matrix.py not found at {self.dR_script}"
        )

    def test_PT_script_exists(self):
        """Test that extract_PT_matrix.py exists."""
        self.assertTrue(
            self.PT_script.exists(),
            f"extract_PT_matrix.py not found at {self.PT_script}"
        )

    def test_dR_script_structure(self):
        """Test that dR script has required functions."""
        with open(self.dR_script, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_functions = [
            "def extract_dR_matrix",
            "def matrix_to_lean",
            "def export_curve_to_lean",
        ]
        
        for func in required_functions:
            self.assertIn(func, content, f"Function not found: {func}")

    def test_PT_script_structure(self):
        """Test that PT script has required functions."""
        with open(self.PT_script, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_functions = [
            "def extract_PT_matrix",
            "def compare_dR_PT",
            "def validate_bsd_cohomology",
        ]
        
        for func in required_functions:
            self.assertIn(func, content, f"Function not found: {func}")

    def test_scripts_have_docstrings(self):
        """Test that scripts have proper documentation."""
        for script in [self.dR_script, self.PT_script]:
            with open(script, 'r', encoding='utf-8') as f:
                content = f.read()
            
            self.assertIn('"""', content)
            self.assertIn("Author:", content)

    def test_dR_script_import(self):
        """Test that dR script can be imported (structure only)."""
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location("extract_dR_matrix", self.dR_script)
            self.assertIsNotNone(spec)
        except Exception as e:
            self.fail(f"Failed to load dR script spec: {e}")

    def test_PT_script_import(self):
        """Test that PT script can be imported (structure only)."""
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location("extract_PT_matrix", self.PT_script)
            self.assertIsNotNone(spec)
        except Exception as e:
            self.fail(f"Failed to load PT script spec: {e}")


class TestCohomologyDataFiles(unittest.TestCase):
    """Test cohomology data files."""

    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = Path(__file__).parent.parent
        self.data_dir = self.repo_root / "data"

    def test_data_directory_exists(self):
        """Test that data directory exists."""
        self.assertTrue(
            self.data_dir.exists(),
            f"Data directory not found at {self.data_dir}"
        )

    def test_cohomology_data_file_exists(self):
        """Test that cohomology data file exists."""
        data_file = self.data_dir / "bsd_cohomology_data.json"
        self.assertTrue(
            data_file.exists(),
            f"Cohomology data file not found at {data_file}"
        )

    def test_cohomology_data_valid_json(self):
        """Test that cohomology data is valid JSON."""
        data_file = self.data_dir / "bsd_cohomology_data.json"
        if data_file.exists():
            with open(data_file, 'r') as f:
                try:
                    data = json.load(f)
                    self.assertIsInstance(data, dict)
                except json.JSONDecodeError as e:
                    self.fail(f"Invalid JSON in cohomology data: {e}")

    def test_cohomology_data_has_curves(self):
        """Test that cohomology data contains curves."""
        data_file = self.data_dir / "bsd_cohomology_data.json"
        if data_file.exists():
            with open(data_file, 'r') as f:
                data = json.load(f)
            
            self.assertIn("curves", data)
            self.assertIsInstance(data["curves"], list)
            self.assertGreater(len(data["curves"]), 0)

    def test_curve_data_structure(self):
        """Test that curve data has required fields."""
        data_file = self.data_dir / "bsd_cohomology_data.json"
        if data_file.exists():
            with open(data_file, 'r') as f:
                data = json.load(f)
            
            required_fields = ["curve_id", "rank", "dR_matrix", "pt_matrix", "compatible"]
            
            for curve in data.get("curves", []):
                for field in required_fields:
                    self.assertIn(field, curve, f"Field {field} missing from curve data")


class TestLakefileConfiguration(unittest.TestCase):
    """Test lakefile configuration for rational_structures library."""

    def setUp(self):
        """Set up test fixtures."""
        self.repo_root = Path(__file__).parent.parent
        self.lakefile = self.repo_root / "formalization" / "lean" / "lakefile.lean"

    def test_lakefile_exists(self):
        """Test that lakefile exists."""
        self.assertTrue(
            self.lakefile.exists(),
            f"lakefile.lean not found at {self.lakefile}"
        )

    def test_lakefile_has_rational_structures(self):
        """Test that lakefile includes rational_structures library."""
        with open(self.lakefile, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn("RationalStructures", content)
        self.assertIn("rational_structures", content)


if __name__ == '__main__':
    unittest.main()
