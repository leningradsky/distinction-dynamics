/-
  DD Level 1: Distinction (T0-T3) — Lean 4
-/

namespace DD.L01

-- T0: Empty has no constructors (Ø impossible)
theorem T0 : Empty → False := fun h => h.elim

-- T1: Distinction exists
theorem true_ne_false : true ≠ false := Bool.noConfusion

theorem T1 : ∃ (x y : Bool), x ≠ y :=
  ⟨true, false, true_ne_false⟩

-- T2: Binary structure  
theorem T2 (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

-- T3: Codes are distinguishable
inductive U where
  | BOOL : U
  | UNIT : U

theorem BOOL_ne_UNIT : U.BOOL ≠ U.UNIT := U.noConfusion

theorem T3 : ∃ (x y : U), x ≠ y :=
  ⟨U.BOOL, U.UNIT, BOOL_ne_UNIT⟩

-- Done
theorem L01_done : True := trivial

end DD.L01
