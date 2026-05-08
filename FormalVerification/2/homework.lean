-- Session 2: Exercises
-- ====================

-- 1. Define `mult : Nat -> Nat -> Nat` and `factorial : Nat -> Nat` for `Natural` numbers.
inductive Natural where
  | zero : Natural
  | succ : Natural -> Natural

open Natural

def add x y := match x with
  | zero   => y
  | succ z => succ (add z y)

def mult (x: Natural) (y: Natural) : Natural :=
  match x with
  | zero => zero
  | succ z => add y (mult z y)

def factorial (x: Natural) : Natural :=
  match x with
  | zero => succ zero
  | succ z => mult (succ z) (factorial z)

def five := succ (succ (succ (succ (succ zero))))
def three := succ (succ (succ zero))
def one := succ zero

#eval mult three one
#eval factorial three


-- 2. Translate the following logical statements into types using Curry–Howard correspondence:
--     - `P /\ (Q \/ R)`
--     - `(P -> Q) -> R`
--     - `~ ~ ~ P`


variable (P Q R : Prop)

def t1 : Prop := P ∧ (Q ∨ R)
def t2 : Prop := (P -> Q) -> R
def t3 : Prop := ¬ ¬ ¬ P


-- 3. Does there exist a function of type `False -> P` for any and every `P`. Why? What does this fact correspond to in logic?

def falseImpliesAnything (P : Prop) : False -> P :=
  sorry


-- 4. Try to prove the following propositions using the principle of induction:
--     - `forall n : Nat. n = n + 0`
--     - `forall x y : List Nat. length (x ++ y) = length x + length y`

-- Induction keyword expects a base case and an inductive case.
-- In the inductive case, we can assume the inductive hypothesis (ih) that the proposition holds for smaller values.
theorem nat_eq_nat_add_zero : forall n : Nat, n = n + 0 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
    rfl

theorem nat_eq_zero_add_nat : forall n : Nat, n = 0 + n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
    exact Nat.add_comm (n+1) 0

-- List Constructors: "Nil" and "Cons x xs"
theorem length_append : forall x y : List Nat, List.length (x ++ y) = List.length x + List.length y := by
  intro x y
  induction x with
  | nil =>
      simp
  | cons a xs ih =>
      simp [ih, Nat.add_assoc, Nat.add_comm]
