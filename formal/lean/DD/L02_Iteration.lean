/-
  DD Level 2: Iteration (T4) — Lean 4
-/

namespace DD.L02

-- Monoid laws (built-in for Nat)
theorem add_identity_l (n : Nat) : 0 + n = n := Nat.zero_add n
theorem add_identity_r (n : Nat) : n + 0 = n := Nat.add_zero n
theorem add_assoc (m n p : Nat) : (m + n) + p = m + (n + p) := Nat.add_assoc m n p

-- T4: Irreversibility — suc n ≠ n
theorem T4 : ∀ n : Nat, n + 1 ≠ n := by
  intro n h
  omega

-- Alternative direct proof
theorem T4' (n : Nat) : Nat.succ n ≠ n := by
  induction n with
  | zero => exact Nat.noConfusion
  | succ n ih => intro h; exact ih (Nat.succ.inj h)

-- No maximum
theorem no_max (n : Nat) : n < n + 1 := Nat.lt_succ_self n

-- Done
theorem L02_done : True := trivial

end DD.L02
