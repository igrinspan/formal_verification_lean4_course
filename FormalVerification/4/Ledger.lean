import Mathlib.Tactic

abbrev Ident := Nat
abbrev Amount := Nat

structure Account where
  id : Ident
  name : String
  bal : Amount
  deriving Repr, BEq, DecidableEq

abbrev Ledger := List Account

def addAccount (l : Ledger) (a : Account) : Ledger :=
  if l.any (fun x => x.id == a.id)
  then l
  else a :: l

theorem addAccount_length (l : Ledger) (a : Account) :
  (addAccount l a).length = l.length ∨ (addAccount l a).length = l.length + 1
  := by
  unfold addAccount
  split <;> simp

theorem addAccount_exists (l : Ledger) (a : Account) :
  a ∈ l -> (addAccount l a).length = l.length := by
  intro a_in_l
  unfold addAccount
  split -- split_ifs with if_any
  next => rfl
  next =>
    -- Como sabemos que en realidad a ∈ l, podemos crear una nueva hipótesis que sea
    -- lo contrario al goal. Demostramos esa hipotesis y después podemos hacer contradiction
    -- porque tenemos dos hipótesis que se contradicen.
    have if_any_contra : List.any l (λ x => x.id == a.id) = true := by
      simp [List.any_eq_true] -- este lema transforma el List.any en un existencial
      use a -- con USE, proveemos un witness a ese existencial. Nos viene perfecto porque sabemos que a ∈ l.
    contradiction

theorem addAccount_not_exists (l : Ledger) (a : Account) :
  ¬ (l.any (λ x => x.id == a.id) = true) -> (addAccount l a).length = l.length + 1 := by
  intro notexists
  unfold addAccount
  split
  case isTrue => contradiction
  case isFalse => rfl


theorem addAccount_idem (l : Ledger) (a : Account) :
  addAccount (addAccount l a) a = addAccount l a := by
  unfold addAccount
  split
  case isTrue h1 => rfl
  case isFalse h2 =>
    split
    case isTrue h3 => rfl
    case isFalse h4 =>
    exfalso
    unfold Not at *
    apply h4
    simp -- de alguna manera, simp va aplicando lemas de listas y de List.any
    -- (a :: l).any fun x => x.id == a.id
    -- = (a.id == a.id) || l.any fun x => x.id == a.id   -- por List.any_cons
    -- = true || l.any fun x => x.id == a.id             -- por BEq.refl (o beq_self_eq_true)
    -- = true

def getBalance (l : Ledger) (id : Ident) : Option Amount :=
  match l with
  | [] => none
  | h :: t =>
    if (h.id == id) then some h.bal
    else getBalance t id

def getSupply (l : Ledger) : Amount :=
  l.foldl (λ accum account => accum + account.bal) 0


def getSupplyRecursive (l : Ledger) : Amount :=
    match l with
  | [] => 0
  | h :: t => h.bal + getSupplyRecursive t


def debitAccount (l : Ledger) (id : Ident) (amt : Amount) : Option Ledger :=
  match l with
  | [] => none
  | h :: t =>
    if (h.id == id) then
      if (h.bal >= amt) then
        some ({ h with bal := h.bal - amt } :: t)
      else none
    else Functor.map (fun t' => h :: t') (debitAccount t id amt)

def creditAccount (l : Ledger) (id : Ident) (amt : Amount) : Option Ledger :=
    match l with
  | [] => none
  | h :: t =>
    if (h.id == id) then
      some ({ h with bal := h.bal + amt } :: t)
    else
      Option.map (fun t' => h :: t') (creditAccount t id amt)


def existsInLedger (l : Ledger) (id: Ident) : Bool :=
  l.any (λ account => account.id == id)

def transferFunds (l : Ledger) (fromId : Ident) (toId : Ident) (amt : Amount) : Option Ledger :=
  if ((existsInLedger l fromId) && (existsInLedger l toId)) then
    do
    let l1 <- debitAccount l fromId amt
    creditAccount l1 toId amt
  else
    none

/- Examples / tests - create accounts, ledger and evaluate functions -/
def a1 : Account := { id := 1, name := "Alice", bal := 100 }
def a2 : Account := { id := 2, name := "Bob", bal := 50 }
def a3 : Account := { id := 3, name := "Carol", bal := 0 }

def ledger0 : Ledger := [a1, a2]

#eval getBalance ledger0 1           -- some 100
#eval getBalance ledger0 3           -- none
#eval getSupply ledger0              -- 150
#eval getSupplyRecursive ledger0     -- 150

#eval debitAccount ledger0 1 30      -- some ledger with Alice bal 70
#eval debitAccount ledger0 2 100     -- none (insufficient funds)

#eval creditAccount ledger0 2 20     -- some ledger with Bob bal 70

#eval transferFunds ledger0 1 2 40   -- some ledger (Alice 60, Bob 90)
#eval transferFunds ledger0 1 3 10   -- none (toId doesn't exist)

#eval existsInLedger ledger0 2        -- true
