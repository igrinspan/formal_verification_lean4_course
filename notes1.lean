#eval 3  + 4

#check 0

#check (1: Int)

#eval 3-4

#eval (3-4:Int)

#eval (some 2)


-- #eval if 2 == 3 then "abc" else 2 FAILS bc types.
#eval if 2 == 3 then "abc" else "a"

def double (x: Nat) : Nat := x+x

def square : Nat -> Nat := fun x => x * x

def negate (b: Bool): Bool :=
  match b with
  | true => false
  | false => true

--def factorial (n: Nat) : Nat :=
--  match n with
--  |


-- Recursion?
-- id x = id x

-- def factorial (x: Nat) : Nat := if x == 0 then 1 else x * factorial (x-1) AS IT IS DOES NOT WORK.
-- To do recursion we have to prove x-1 is smaller than x.

structure Point where
  x: Float
  y: Float

def p : Point := {x := 1, y := 2 }
def q : Point := {x := 3, y := 2 }

-- #eval (p == q)
instance:  BEq Point where
  beq p q := p.x == q.x && p.y == q.y

#eval p == q

def xproj (p: Point) : Point := {p with y := 0}

#eval xproj p

structure Person where
  id: Nat
  name: String

def person: Person := {id := 1, name := "Alice"}
#eval person

-- Exercise: change name of person to uppercase.

-- Inductive types

inductive Direction where
  | north
  | south
  | west
  | east

#eval (Direction.north: Direction)

-- Shape: circle or rectangle
-- constructors: start with lowercase letters
inductive Shape where
  | circle : Float -> Shape
  | rectangle: Float -> Float -> Shape

def area (s: Shape) : Float :=
  match s with
  | Shape.circle r =>  3.14 * (r ^ 2)
  | Shape.rectangle l b => l * b

#eval (area (Shape.circle 4))
#eval (area (Shape.rectangle 3 4))

-- Polymorphism
#check List
-- List.{u} (α : Type u) : Type u

-- Identity function (parametric function):
def identity (t: Type) (x: t) := x
-- So to evaluate it first we pass the type and then the value.
#eval identity Nat 7
#eval identity String "Hi"

-- t is the type.
inductive Lista t where
  | null: Lista t
  | cons: t -> Lista t -> Lista t

#check Lista.cons

def length (a: Type) (xs: Lista a): Nat :=
  match xs with
  | Lista.null => 0
  | Lista.cons _ ys => 1 + length a ys

#eval (length String Lista.null)
#eval (length String (Lista.cons "a" Lista.null))

#check List.head? -- Returns Option bc of the empty list case.
-- List.head?.{u} {α : Type u} : List α → Option α

#eval List.head? ([] : List Nat)
#eval List.head? (α := Nat) [2, 3]
-- Question mark to say it returns Option.

-- Typeclasses.
-- BEq, tostring...

-- Namespaces

namespace X
  def y := 2
  #eval y
end X

#eval X.y

-- Functors
#check (some 7).map
-- fun f => Option.map f (some 7) : (Nat → ?m.5) → Option ?m.5

#eval (some 7).map (fun x => x + 1)
#eval [1, 2, 3].map (fun x => x + 1)
#eval (some 7).map (· + 1) -- dot notation

#check some 7
-- Now we need to provide a function.

-- Monads (ex. IO)
def hello := IO.println "hello, world"
#check hello -- IO Unit.
#eval hello

def ask := do
  IO.println "Name?"
  let stdin <- IO.getStdin
  let name <- stdin.getLine
  IO.println ("hello, " ++ name)


-- Coding Exercise: Ledger (like a list of accounts)

structure Account where
  id: Nat
  name: String
  bal: Nat
  deriving Repr

def alice: Account := {id:= 1, name:= "Alice", bal:= 0}

-- A ledger is just a list of accounts.
-- Ledger List Account
def createAccount (l : List Account) (id: Nat) (name: String) (bal: Nat) : List Account :=
  if l.any (fun p => p.id == id)
  then l
  else (({id := id, name := name, bal := bal}) :: l)

#eval createAccount [alice] 2 "Bob" 100


-- Can also use arrows for the function declarations.
def creditAccount (l: List Account) (id: Nat) (amt: Nat) : List Account := sorry -- Exercise


-- if list is empty, return empty list
-- if amount is more than balance, error. That's why Option.
def debitAccount (l: List Account) (id: Nat) (amt: Nat) : Option (List Account) :=  -- Exercise
  match l with
  | [] => l
  | h :: t =>
    if (h.id == id)
    then if (h.bal >= amt)
      then some ({h with bal := h.bal - amt} :: t)
      else none
    else do
      let t' <- debitAccount t id amt
      return (h :: t')

#eval debitAccount (createAccount [alice] 2 "Bob" 100) 2 35
