
plusidex1 : (n, m : Nat) -> (n = m) -> n + n = m + m
plusidex1 n m prf = rewrite prf in Refl

-- Exercise 8.1
plusidex2 : (n, m, o : Nat) -> (n = m) -> (m = o) -> n + m = m + o
plusidex2 n m o prf prf1 = rewrite prf in (rewrite prf1 in Refl)

-- Exercise 8.2
multS1 : (n, m : Nat) -> (m = S n) -> m * (1 + n) = m * m
multS1 n m prf = rewrite prf in Refl

-- Random practice proof
mu : (n, m : Nat) -> (m = 50) -> (n = m + 50) -> 200 = n + n
mu n m prf prf1 = rewrite prf1 in rewrite prf in Refl
