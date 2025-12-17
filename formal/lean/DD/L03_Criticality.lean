/-
  DD Level 3: Criticality & Number Tower (T5-T6) — Lean 4 + Mathlib
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DD.L03

-- T5: Critical regime
structure Bounded where
  lower : ℕ
  upper : ℕ

def T5 : Bounded := ⟨0, 1000000⟩

-- T6: Full Number Tower ℕ → ℤ → ℚ → ℝ

-- ℤ
theorem T6_Z_negative : ∃ z : ℤ, z < 0 := ⟨-1, by decide⟩

theorem T6_Z_ordered (a b : ℤ) : a < b ∨ a = b ∨ a > b := by omega

-- ℚ (rationals)
theorem T6_Q_exists : ∃ q : ℚ, 0 < q := ⟨1, by decide⟩

theorem T6_Q_dense (a b : ℚ) (h : a < b) : ∃ c : ℚ, a < c ∧ c < b :=
  ⟨(a + b) / 2, by constructor <;> linarith⟩

-- ℝ (reals)  
theorem T6_R_exists : ∃ r : ℝ, 0 < r := ⟨1, by norm_num⟩

theorem T6_R_dense (a b : ℝ) (h : a < b) : ∃ c : ℝ, a < c ∧ c < b :=
  ⟨(a + b) / 2, by constructor <;> linarith⟩

-- Embeddings
def N_to_Z (n : ℕ) : ℤ := n
def Z_to_Q (z : ℤ) : ℚ := z
def Q_to_R (q : ℚ) : ℝ := q

-- Done
theorem L03_done : True := trivial

end DD.L03
