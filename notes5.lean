import Blaster

structure Vault where
  locked : Bool
  amount : Int
  password : String
  deriving Repr

inductive Action where
  | deposit : Int -> Action
  | claim : String -> Action
  deriving Repr


open Action

-- Contract
def contract (s: Vault) (a: Action) : Option Vault :=
  match a with
  | deposit n =>
    if n >= 0
      then some { password := s.password, locked := s.locked, amount := s.amount + n }
      else none
  | claim p =>
    if p == s.password
      then if s.locked
        then some { password := s.password, locked := false, amount := 0 }
        else none
    else none

def start : Vault := { locked := true, amount := 100, password := "secret" }


-- Invariant
def Open (s: Vault) : Prop := s.amount >= 0

def Done (s: Vault) : Prop := s.locked = false -> s.amount = 0

-- Test
theorem deposit_works : contract start (deposit 10) = some { locked := true, amount := 110, password := "secret" } := by
  rfl

-- Theorem
-- Deposit preserves the Open property
-- We have a starting state s, and a closing state s'
theorem deposit_open : Open s -> contract s (deposit n) = some s' -> Open s' := by
  intro hOpen hStep
  unfold contract at hStep
  unfold Open at *
  by_cases h: n >= 0
  next =>
    simp [h] at hStep
    blaster
  next =>
    simp [h] at hStep

theorem deposit_open_ : Open s -> contract s (deposit n) = some s' -> Open s' := by
  blaster

--
theorem claim_done_ : contract s (claim p) = some s' -> Done s' := by
  blaster

theorem claim_done : contract s (claim p) = some s' -> Done s' := by
  intro hStep
  unfold Done
  unfold contract at hStep
  intro hLockFalse
  by_cases hPass : p = s.password
  next =>
    simp [hPass] at hStep
    by_cases hLocked : s.locked
    next =>
      simp [hLocked] at hStep
      blaster
    next =>
      simp [hLocked] at hStep
  next =>
    simp [hPass] at hStep
