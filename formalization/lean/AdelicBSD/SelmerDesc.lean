/-
Selmer Group Descriptors
=========================

This module defines Selmer group structures and related cohomological tools.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
-/

import Mathlib.AlgebraicGeometry.EllipticCurve
import Mathlib.NumberTheory.NumberField.Basic

namespace AdelicBSD

open EllipticCurve

/-- Selmer group descriptor for an elliptic curve over ℚ -/
axiom SelmerGroup (E : EllipticCurve ℚ) : Type

/-- Dimension of Selmer group -/
axiom selmer_dimension (E : EllipticCurve ℚ) : ℕ

end AdelicBSD
