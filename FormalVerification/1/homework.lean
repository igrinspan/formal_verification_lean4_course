-- Session 1: Exercises
-- ====================

-- 1. Implement functions `and`, `or`, and `xor` for values of type `Bool`.
def land (a: Bool) (b: Bool): Bool :=
  match a with
    | true => b
    | false => false

def lor (a: Bool) (b: Bool): Bool :=
  match a with
    | true => true
    | false => b

def lxor (a: Bool) (b: Bool): Bool :=
  a != b


-- 2. Write a function `upper` which takes a `Person` and returns a `Person`
-- where the `name` is changed to uppercase.
structure Person where
  id : Nat
  name : String

def upper (p: Person): Person :=
  { p with name := p.name.toUpper }


-- 3. Implement a simple instance of `BEq` for `Direction` and implement separate
-- instances of `Ord` for `Person`, numerically and lexicographically.
inductive Direction where
  | north
  | south
  | west
  | east

instance : BEq Direction where
  beq a b := match a, b with
    | Direction.north, Direction.north => true
    | Direction.south, Direction.south => true
    | Direction.west,  Direction.west  => true
    | Direction.east,  Direction.east  => true
    | _,      _      => false

namespace Numeric
instance : Ord Person where
  compare p1 p2 :=
    if p1.id > p2.id then .gt
    else if p1.id < p2.id then .lt
    else .eq
end Numeric

namespace NumericUsingNatOrd
instance : Ord Person where
  compare p1 p2 := compare p1.id p2.id
end NumericUsingNatOrd

namespace Lexicographic
instance : Ord Person where
  compare p1 p2 := compare p1.name p2.name
end Lexicographic


-- 4. Find out and interpret the type signatures of the terms `[]`, `Just`, `Right`.
-- Which syntactic/semantic features in Lean make parametric
-- polymorphism more clearer/rigorous compared to Haskell?
#check []



-- 5. Write a function which filters a `List Nat` based on a given predicate? Why is `filter` easy to define but not `factorial` which seems more trivial?
def filterNats (p: Nat -> Bool) (xs: List Nat): List Nat :=
  match xs with
  | [] => []
  | x :: xs' =>
    if p x then x :: filterNats p xs'
    else filterNats p xs'

-- I assume it's something related with inductive types and structural recursion.
-- Here we match with different constructors. Lean knows xs' is smaller than x :: xs'.


-- 6. Complete the implementation of `creditAccount` and `transferFunds` in the Ledger model.
