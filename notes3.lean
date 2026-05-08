import Blaster

#check "abc"

#check String

#check Nat

#check Type

#check Type 1


-- Funcion de Nat a Nat se declara en general asi.
-- def double (x: Nat) : Nat := x + x

-- Teoremas
-- theorem t (P: Prop) : P -> P
-- Para demostrar t, tenemos que dar un valor de ese tipo.
-- Entonces le damos una funcion que recibe un P y devuelve un P.
theorem t (P: Prop) : P -> P :=
  λ p => p

#check t


theorem modus_ponens (P Q: Prop) : (P -> Q) -> P -> Q :=
  λ f p => f p

#check modus_ponens


theorem modus_ponens_tactic (P Q: Prop) : (P -> Q) -> P -> Q := by
  intro f p -- to name the variables
  exact (f p)
-- If we do apply f instead, we then only need to prove p.

theorem conjuncion (P Q R T : Prop) : P -> Q -> (P -> R) -> (Q -> T) -> (R ∧ T) := by
  intro p q f g
  constructor
  . exact (f p)
  . exact (g q)

-- Now with P ∧ Q instead.
theorem cases_demo (P Q R T : Prop) : (P ∧ Q) -> (P -> R) -> (Q -> T) -> (R ∧ T) := by
  intro pq f g
  cases pq with -- introduces left and right, of types P and Q respectively.
    | intro p q =>
      constructor
      . exact (f p)
      . exact (g q)


-- INDUCTION tactic
-- We want to prove base case (zero, etc.).
theorem add_zero (n: Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
  -- Now we need to prove that 0 + (m + 1) equals (m + 1)
    have h : 0 + (m + 1) = (0 + m) + 1 := Nat.add_assoc 0 m 1
    rw [h]
    rw [ih]

-- We know about the associativity of addition. So we use it.


theorem add_zero_simp (n: Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp -- simp uses already known lemmas of the built in library and applies them.
-- Be careful, simp hides steps. We can see them using print.

#print add_zero_simp


theorem add_zero_blaster (n: Nat) : 0 + n = n := sorry
