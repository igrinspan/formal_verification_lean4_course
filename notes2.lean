inductive Natural where
  | zero : Natural
  | succ : Natural -> Natural

#check Natural.zero

#eval Natural.succ Natural.zero

-- Different ways of defining a data type.
-- Structures are just records with named fields.
-- Abbreviations are just aliases for existing types.
-- Inductive types are more general and can have multiple constructors.
--    It's what's used to define types.


def zero := Natural.zero
def two := Natural.succ (Natural.succ Natural.zero)

def isZero (x: Natural) : Bool :=
  match x with
  | Natural.zero => true
  | Natural.succ _ => false

#eval isZero zero
#eval isZero two

def add (x: Natural) (y: Natural) : Natural :=
  match x with
  | Natural.zero => y
  | Natural.succ z => Natural.succ (add z y)

#eval 1 + 1 = 3
#eval 1 + 1 == 3
