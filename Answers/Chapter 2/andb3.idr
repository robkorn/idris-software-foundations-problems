
module Andb3

andb3 : (a : Bool) -> (b : Bool) -> (c : Bool) -> Bool
andb3 True True True = True
andb3 a b c = False


tabt1 : (andb3 True True True) = True
tabt1 = Refl

tabt2 : (andb3 False True True) = False
tabt2 = Refl

tabt3 : (andb3 True False True) = False
tabt3 = Refl

tabt4 : (andb3 True True False) = False
tabt4 = Refl

tabt5 : (andb3 True False False) = False
tabt5 = Refl

tabt6 : (andb3 False True False) = False
tabt6 = Refl

tabt7 : (andb3 False False True) = False
tabt7 = Refl

tabt8 : (andb3 False False False) = False
tabt8 = Refl

tabt9 : (andb3 False True True) = False
tabt9 = Refl


