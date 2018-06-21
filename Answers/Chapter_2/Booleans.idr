
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

public export
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


-- Exercise 11.1
idAppTwiceF : (f : Bool -> Bool) -> (idp : (x : Bool) -> f x = x) -> f (f False) = False
idAppTwiceF f idp = rewrite idp False in rewrite idp False in Refl

idAppTwiceT : (f : Bool -> Bool) -> (idp : (x : Bool) -> f x = x) -> f (f True) = True
idAppTwiceT f idp = rewrite idp True in rewrite idp True in Refl

idAppTwice : (f : Bool -> Bool) -> ((x : Bool) -> f x = x) -> (b : Bool) -> f (f b) = b
idAppTwice f idp False = idAppTwiceF f idp
idAppTwice f idp True = idAppTwiceT f idp

-- Exercise 11.1 - 2
negAppTwiceF : (f : Bool -> Bool) -> (g : (x : Bool) -> f x = negb x) -> f (f False) = False
negAppTwiceF f g = rewrite g False in rewrite g True in Refl

negAppTwiceT : (f : Bool -> Bool) -> (g : (x : Bool) -> f x = negb x) -> f (f True) = True
negAppTwiceT f g = rewrite g True in rewrite g False in Refl

negAppTwice : (f : Bool -> Bool) -> ((x : Bool) -> f x = negb x) -> (b : Bool) -> f (f b) = b
negAppTwice f g False = negAppTwiceF f g
negAppTwice f g True = negAppTwiceT f g

