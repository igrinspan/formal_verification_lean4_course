-- 1. Given `P Q R : Prop`, prove the following theorems:
--   - `P ∧ Q -> Q ∧ P`
--   - `P ∨ Q -> (¬ P) -> Q`
--   - `P ∨ Q -> (P -> R) -> (Q -> R) -> R`


theorem theorem1 (P Q : Prop) : (P ∧ Q) -> Q ∧ P := by
  intro pq
  cases pq with
  | intro p q =>
    constructor
    . exact q
    . exact p

theorem theorem2 (P Q : Prop) : P ∨ Q -> (¬ P) -> Q := by
  intro pq notp
  unfold Not at notp
  cases pq with
  | inr hq => exact hq
  | inl hp => exact False.elim (notp hp)


theorem theorem3 (P Q R : Prop) : P ∨ Q -> (P -> R) -> (Q -> R) -> R := by
  intro pq pr qr
  cases pq with
  | inl hp => exact pr hp
  | inr hq => exact qr hq

-- 2. Given `P Q R : Prop`, prove the De Morgan Law (you may need `Classical.em` in one of these):
--   - `¬ (P ∧ Q) <-> ¬ P ∨ ¬ Q`
--   - `¬ (P ∨ Q) <-> ¬ P ∧ ¬ Q`

theorem morgan1 (P Q : Prop) : ¬ (P ∧ Q) <-> ¬ P ∨ ¬ Q := by
  constructor
  . intro npq
    unfold Not at *
    have lem:= Classical.em P
    cases lem with
    | inl p =>
      right
      intro q
      exact (npq (And.intro p q))
    | inr np =>
      unfold Not at *
      left
      exact np
  . intro npnq
    cases npnq with
    | inl np =>
      unfold Not at *
      intro pq
      exact np pq.1
    | inr nq =>
      unfold Not at *
      intro pq
      exact nq pq.2


theorem morgan2 (P Q : Prop) : ¬ (P ∨ Q) <-> ¬ P ∧ ¬ Q := by
  constructor
  . intro npq
    unfold Not at *
    constructor
    . intro p
      exact npq (Or.inl p)
    . intro q
      exact npq (Or.inr q)
  . intro npnq
    unfold Not at *
    intro pq
    cases pq with
    | inl p => exact npnq.1 p
    | inr q => exact npnq.2 q



-- 3. Given `a b c : Nat`, prove the following theorems:
--   - `a + 1 = 1 + a`
--   - `a * 0 = 0`
--   - `a * b = b * a`
--   - `a * (b + c) = a * b + a * c`

theorem ex1 (a: Nat) : a + 1 = 1 + a := by
  exact Nat.add_comm a 1

theorem ex2 (a: Nat) : a * 0 = 0 := by
  exact Nat.mul_zero a

theorem ex3 (a b: Nat) : a * b = b * a := by
  exact Nat.mul_comm a b

theorem ex4 (a b c: Nat) : a * (b + c) = a * b + a * c := by
  exact Nat.mul_add a b c


-- 4. Given `a b : Bool`, prove the following theorems:
--   - `a && b = b && a`
--   - `not (not a) = a`
--   - `not (a || b) = not a && not b`

theorem boolEx1 (a b : Bool) : (a && b) = (b && a) := by
  exact Bool.and_comm a b

theorem boolEx2 (a : Bool) : not (not a) = a := by
  exact Bool.not_not a

theorem boolEx3 (a b : Bool) : (not (a || b)) = (not a && not b) := by
  exact Bool.not_or a b

-- 5. Given `a b : List a`, prove the following theorems:
--   - `(x ++ y).length = x.length + y.length`
--   - `(reverse x).length = x.length`
--   - `x.reverse.reverse = x`

theorem listTheorem1 (x y : List a) : (x ++ y).length = (x.length + y.length) := by
  exact List.length_append

theorem listTheorem2 (x : List a) : (x.reverse).length = x.length := by
  exact List.length_reverse

theorem listTheorem3 (x : List a) : x.reverse.reverse = x := by
  exact List.reverse_reverse x
