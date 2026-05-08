import Blaster


-- SAT intro
-- Only boolean expressions

-- SMT
-- Introduces linear arithmetic, arrays, etc.
-- SMT = SAT solver + different theory solvers for different domains.

/-

Z3 = SMT solver
input: formula
output: sat/unsat

Blaster uses Z3 as backend.

Blaster  simplifies and optimizes Lean goals into SMT formulas and calls Z3.

-/

#check False

-- ¬ Q = Q -> False

theorem modus_tollens (P Q: Prop) : (P -> Q) -> ¬ Q -> ¬ P := by
  intro f nq
  unfold Not at *
  intro p
  exact (nq (f p))

theorem dni (P: Prop) : P -> ¬ (¬ P) := by
  intro p np
  unfold Not at *
  exact (np p)


-- in "constructive logic" this is not necessarily true
theorem dne (P: Prop) : ¬ (¬ P) -> P := by
  unfold Not
  have lem:= Classical.em P
  cases lem with
    | inl p => exact (λ _ => p)
    | inr np =>
      intro h
      unfold Not at np
      exfalso
      exact (h np)

theorem add_commutative (x y: Nat) : x + y = y + x := by
  induction x with
  | zero => simp
  | succ z ih => simp [Nat.succ_add, Nat.add_assoc, ih]

theorem add_commutative_bl (x y: Nat) : x + y = y + x := by
  blaster
