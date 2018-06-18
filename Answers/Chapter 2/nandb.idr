
module Nandb

nandb : (a : Bool) -> (b : Bool) -> Bool
nandb True True = False
nandb a b = True

tn1 : (nandb True True) = False
tn1 = Refl
tn2 : (nandb True False) = True
tn2 = Refl
tn3 : (nandb False False) = True
tn3 = Refl
tn4 : (nandb False True) = True
tn4 = Refl
