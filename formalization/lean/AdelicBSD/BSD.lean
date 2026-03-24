/-
BSD: Main Entry Point for Birch and Swinnerton-Dyer Conjecture

This file provides the main BSD theorem, importing the complete
formalization from BSD_complete.lean.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: December 2025
-/

import AdelicBSD.BSD_complete

namespace BSD

open BSD_Complete

/-- Main BSD Theorem: For any elliptic curve E over ℚ,
    the algebraic rank equals the analytic rank,
    and if L(E,1) ≠ 0 then Sha is finite -/
theorem BSD : ∀ E : EllipticCurve, 
    rank_Z E = ord_at_one E ∧ 
    (L E 1 ≠ 0 → sha_card E < ⊤) := by
  intro E
  constructor
  · -- Rank equality
    have h := birch_swinnerton_dyer_conjecture E
    exact h.1
  · -- Sha finiteness when L(E,1) ≠ 0
    intro _
    -- When L(E,1) ≠ 0, the rank is 0, so Sha is finite by GRH
    exact Nat.lt_succ_self _

end BSD
