
plusidex1 : (n, m : Nat) -> (n = m) -> n + n = m + m
plusidex1 n m prf = rewrite prf in Refl

-- Exercise 8.1
plusidex2 : (n, m, o : Nat) -> (n = m) -> (m = o) -> n + m = m + o
plusidex2 n m o prf prf1 = rewrite prf in (rewrite prf1 in Refl)


