
module Simplification

plusZN : (n : Nat) -> 0 + n = n
plusZN n = Refl

plusNZ : (n : Nat) -> n = 0 + n
plusNZ n = Refl

plus1l : (n : Nat) -> 1 + n = S n
plus1l n =  Refl

mult0l : (n : Nat) -> 0 * n = 0
mult0l n = Refl
