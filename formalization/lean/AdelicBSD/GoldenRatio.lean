/-
Golden Ratio Properties

This file formalizes properties of the golden ratio φ = (1 + √5)/2:
- Basic algebraic properties
- The identity φ² = φ + 1
- Cube of golden ratio

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
-/

import AdelicBSD.Constants
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace AdelicBSD

open Real

/-- The golden ratio satisfies φ² = φ + 1 -/
theorem golden_ratio_squared : phi ^ 2 = phi + 1 := by
  unfold phi
  -- φ = (1 + √5)/2
  -- φ² = ((1 + √5)/2)² = (1 + 2√5 + 5)/4 = (6 + 2√5)/4 = (3 + √5)/2
  -- φ + 1 = (1 + √5)/2 + 1 = (3 + √5)/2
  field_simp
  ring_nf
  rw [sq_sqrt]
  · ring
  · norm_num

/-- The golden ratio is positive -/
theorem golden_ratio_positive : 0 < phi := by
  unfold phi
  -- φ = (1 + √5)/2
  -- √5 > 0, so 1 + √5 > 1 > 0
  -- Therefore (1 + √5)/2 > 0
  apply div_pos
  · apply add_pos
    · norm_num
    · apply sqrt_pos.mpr
      norm_num
  · norm_num

/-- Cube of golden ratio equals 2φ + 1 -/
theorem golden_ratio_cube_value : phi ^ 3 = 2 * phi + 1 := by
  -- From φ² = φ + 1, we get φ³ = φ · φ² = φ(φ + 1) = φ² + φ = (φ + 1) + φ = 2φ + 1
  have h := golden_ratio_squared
  calc phi ^ 3 = phi * phi ^ 2 := by ring
    _ = phi * (phi + 1) := by rw [h]
    _ = phi ^ 2 + phi := by ring
    _ = (phi + 1) + phi := by rw [h]
    _ = 2 * phi + 1 := by ring

end AdelicBSD
