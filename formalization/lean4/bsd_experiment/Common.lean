/-
BSD Experiment: Common Definitions

This file contains common definitions shared across all curve formalizations.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.AbsoluteValue

namespace BSDExperiment

/-! ## Weierstrass Coefficient Structure -/

/-- Weierstrass coefficients for an elliptic curve: [a₁, a₂, a₃, a₄, a₆] -/
structure WeierstrassCoeffs where
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  a6 : ℤ
  deriving Repr

/-! ## BSD Formula Types -/

/-- BSD verification result for a single curve -/
structure BSDResult where
  curve_label : String
  rank : ℕ
  analytic_rank : ℕ
  sha_order : ℕ
  bsd_verified : Bool
  deriving Repr

/-- Verification method used -/
inductive VerificationMethod
  | Trivial           -- Rank 0, direct L-value computation
  | GrossZagier       -- Rank 1, Heegner points
  | BeilinsonBloch    -- Rank ≥ 2, algebraic cycles
  | YZZ               -- Yuan-Zhang-Zhang generalization
  | SpectralDescent   -- Internal spectral framework
  deriving Repr

end BSDExperiment
