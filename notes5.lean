import Blaster

/-

Smart Contracts:
- States
- Transitions
- Invariants

Doing formal verification on them means
seeing that transitions on the states
preserve certain invariants.


- Datum (structure)
- Redeemer (transition input)
- Validator

- EUTxO model:
  Each tx:
    1. Consumes old state
    2. Validates constraints
    3. Produces new state

  It maps to function:
  step: State -> Input -> Option State

  (Option bc it may fail).


- Idea of how we would model an Escrow contract.


State:
.amount
.owner
.buyer
.password


An invariant in this case would be
(∀ State) -> Prop

Verification: proving propoerties on transitions.

Questions we may want to answer:
- Can funds get stuck?
- Can invalid states occur?
- Can unauthorized transitions occur?
- Are assets conserved?
- Are state transitions complete?

To test these, we have to turn these questions into functions.


-/


-- We're going to model a Vault "smart contract".
-- The user can basically deposit or claim from the vault.

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
-- It has the logic of how the state changes when
-- an action (using 'redeemers' deposit and claim) is executed.
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
-- We prove that doing the action deposit n on a valid state preserves the Open property.
theorem deposit_open : Open s -> contract s (deposit n) = some s' -> Open s' := by
  intro hOpen hStep
  unfold contract at hStep
  unfold Open at *
  by_cases h: n >= 0
  next =>
    simp [h] at hStep --- acá se resuelve todo el tema de match deposit n with ...
    rw [← hStep]
    show s.amount + n >= 0
    -- tenemos que s.amount >= 0 y n >= 0 en las hipótesis
    omega
  next =>
    simp [h] at hStep

theorem deposit_open_explicit : Open s -> contract s (deposit n) = some s' -> Open s' := by
  intro hOpen hStep
  unfold contract at hStep
  unfold Open at *
  by_cases h: n >= 0
  next =>
    dsimp only at hStep -- dsimp hace la IOTA REDUCTION. matchea el constructor deposit con el case de deposit en el "match".
    -- rw [if_pos h] at hStep
    by_cases h': n >= 0
    next =>
      simp [h'] at hStep
      rw [← hStep]
      show s.amount + n >= 0
      -- tenemos que s.amount >= 0 y n >= 0 en las hipótesis
      omega
    next =>
      contradiction
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
