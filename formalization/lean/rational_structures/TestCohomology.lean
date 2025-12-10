/-
Copyright (c) 2025 José Manuel Mota Burruezo. All rights reserved.
TestCohomology: Executable tests for dRvsPT_Analyzer

Tests the compatibility between de Rham and Perrin-Riou structures
for elliptic curves of rank ≥ 2.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
-/

import RationalStructures.DRvsPTAnalyzer

open BSD.RationalStructures

-- ═══════════════════════════════════════════════════════════════
-- EXECUTABLE TESTS
-- ═══════════════════════════════════════════════════════════════

-- Test 1: Verify curve 5077a1
#eval verify_curve test_5077a1  -- Expected: true

-- Test 2: Verify curve 5942a1  
#eval verify_curve test_5942a1  -- Expected: true

-- Test 3: Verify curve 11131a1
#eval verify_curve test_11131a1  -- Expected: true

-- Test 4: Full test suite
#eval test_suite  -- Expected: true

-- Test 5: Detailed verification results
#eval verify_curve_detailed test_5077a1
#eval verify_curve_detailed test_5942a1
#eval verify_curve_detailed test_11131a1

-- Test 6: Batch verification
#eval verify_all_curves  -- Expected: true

-- ═══════════════════════════════════════════════════════════════
-- ADDITIONAL TEST CASES
-- ═══════════════════════════════════════════════════════════════

/-- Additional test: Custom curve with non-trivial regulator -/
def test_custom_1 : EllipticCohomology := {
  curve_id := "custom_test_1"
  rank := 2
  dR_matrix := !![2, 1; 0, 2]  -- Non-identity but compatible
  pt_matrix := !![2, 1; 0, 2]  -- Same structure
  mw_rank := 2
  rank_ge_two := by decide
}

#eval verify_curve_detailed test_custom_1

/-- Test: Incompatible traces should fail -/
def test_incompatible : EllipticCohomology := {
  curve_id := "incompatible_test"
  rank := 2
  dR_matrix := !![1, 0; 0, 1]  -- Trace = 2
  pt_matrix := !![2, 0; 0, 2]  -- Trace = 4 (different)
  mw_rank := 2
  rank_ge_two := by decide
}

#eval verify_curve test_incompatible  -- Expected: false (traces don't match)

-- ═══════════════════════════════════════════════════════════════
-- THEOREM VERIFICATION
-- ═══════════════════════════════════════════════════════════════

-- Verify that test_5077a1 satisfies comparison
example : compare_dR_PT test_5077a1 := by decide

-- Verify that test_5942a1 satisfies comparison
example : compare_dR_PT test_5942a1 := by decide

-- Verify that test_11131a1 satisfies comparison
example : compare_dR_PT test_11131a1 := by decide

-- ═══════════════════════════════════════════════════════════════
-- SUMMARY
-- ═══════════════════════════════════════════════════════════════

/-- Summary of test results -/
def test_summary : String :=
  let results := testCurves.map verify_curve_detailed
  let compatible_count := results.filter (·.compatible) |>.length
  let total := results.length
  s!"BSD Cohomology Test Summary: {compatible_count}/{total} curves compatible"

#eval test_summary
