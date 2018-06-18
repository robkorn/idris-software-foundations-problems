
module Booleans

infixl 4 /\, \/

data MyBool : Type where
     True : MyBool
     False : MyBool

-- Alternate way of creating the MyBool datatype
-- data MyBool = True | False

negb : Bool -> Bool
negb False = True
negb True = False

andb : (a : Bool) -> (b : Bool) -> Bool
andb False b = False
andb True b = b

orb : (a : Bool) -> (b : Bool) -> Bool
orb False b = b
orb True b = True

-- orb truth table as proofs
to1 : (orb True True) = True
to1 = Refl
to2 : (orb True False) = True
to2 = Refl
to3 : (orb False False) = False
to3 = Refl
to4 : (orb False True) = True
to4 = Refl

(/\) : Bool -> Bool -> Bool
(/\) = andb

(\/) : Bool -> Bool -> Bool
(\/) = orb

to5 : False \/ False \/ True = True
to5 = Refl
