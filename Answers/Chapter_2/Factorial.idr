
module Factorial


facto : Nat -> Nat
facto Z = 1
facto n@(S k) = mult n (fact k)

tf1 : facto 3 = 6
tf1 = Refl

tf2 : facto 5 = mult 10 12
tf2 = Refl



