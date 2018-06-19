
module Numbers

%default total

data MyNat : Type where
     MyZ : MyNat
     MyS : MyNat -> MyNat


pred : (n : Nat) -> Nat
pred Z = Z
pred (S k) = k

minDos : Nat -> Nat
minDos Z = Z
minDos (S k) = Z
minDos (S (S k)) = k

evenb : Nat -> Bool
evenb Z = True
evenb (S (S k)) = evenb k
evenb (S k) = False
-- can also pattern match on (and have it as the 1st or 2nd option):
-- evenb (S Z) = False

oddb : Nat -> Bool
oddb = not . evenb

todd1 : oddb 1 = True
todd1 = Refl
todd2 : oddb 4 = False
todd2 = Refl

myPlus : Nat -> Nat -> Nat
myPlus Z b = b
myPlus (S k) b = S (myPlus k b)

myMult : Nat -> Nat -> Nat
myMult Z b = Z
myMult (S k) b = myPlus b (myMult k b)

tM1 : (mult 3 3) = 9
tM1 = Refl

myMinus : (uno, dos : Nat) -> Nat
myMinus Z _ = Z
myMinus a Z = a
myMinus (S k) (S j) = myMinus k j

tmi1 : (myMinus 5 3) = 2
tmi1 = Refl
tmi2 : (myMinus 0 2352) = 0
tmi2 = Refl

myExp : Nat -> Nat -> Nat
myExp _ Z = 1
myExp b (S j) = myMult b (myExp b j)

tme1 : (myExp 2 3) = 8
tme1 = Refl
tme2 : (myExp 5 2) = 25
tme2 = Refl
