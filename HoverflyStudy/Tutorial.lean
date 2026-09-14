import Hoverfly

add_hoverfly_tactics [
    assumption
    intros
    rfl
    split
    subst_eqs
    rw [Nat.succ_add]
    rw [Nat.add_comm]
    rw [Nat.add_zero]
    rw [Nat.add_succ]
    rw [List.cons_append]
    rw [List.length_cons]
    induction HYP
  ]

/-
Associativity of addition: n + (m + p) is the same as (n + m) + p.
-/
theorem demo_add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  hoverfly /- Place cursor here and open the Infoview to start. -/
