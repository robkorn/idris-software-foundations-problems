
module CaseAnalysis

import Booleans
import Bltnat

-- By using the commumative property of (+) it is easiest just to write (n + 1) as (1 + n) as beq_nat and (+) pattern match on the 1st argument, thus it can't be an unknown
plusft_com : (n : Nat) -> beq_nat (1 + n) 0 = False
plusft_com n = Refl

-- Or case split on the original
plusft : (n : Nat) -> beq_nat (n + 1) 0 = False
plusft Z = Refl
plusft (S k) = Refl

andb_commutative : (b, c : Bool) -> andb b c = andb c b
andb_commutative False False = Refl
andb_commutative False True = Refl
andb_commutative True False = Refl
andb_commutative True True = Refl

-- Alternative
andbcommutative'rhs_1 : (c : Bool) -> False = andb c False
andbcommutative'rhs_1 False = Refl
andbcommutative'rhs_1 True = Refl

andbcommutative'rhs_2 : (c : Bool) -> c = andb c True
andbcommutative'rhs_2 False = Refl
andbcommutative'rhs_2 True = Refl

andbCommutative : (b, c : Bool) -> andb b c = andb c b
andbCommutative False = andbcommutative'rhs_1
andbCommutative True = andbcommutative'rhs_2

-- Exercise 9.1
andbTelim2F : (c : Bool) -> (prf : andb False c = True) -> c = True
andbTelim2F False prf = prf
andbTelim2F True prf = Refl

andbTelim2T : (c : Bool) -> (prf : andb True c = True) -> c = True
andbTelim2T False prf = prf
andbTelim2T True prf = Refl

andbTelim2 : (b, c : Bool) -> (andb b c = True) -> c = True
andbTelim2 False c prf = andbTelim2F c prf
andbTelim2 True c prf = andbTelim2T c prf


-- Exercise 9.2
zeroNbeqPlusZ : False = False
zeroNbeqPlusZ = Refl

zeroNbeqPlus1S : (k : Nat) -> False = False
zeroNbeqPlus1S k = Refl

zeroNbeqPlus1 : (n : Nat) -> beq_nat 0 (n + 1) = False
zeroNbeqPlus1 Z = zeroNbeqPlusZ
zeroNbeqPlus1 (S k) = zeroNbeqPlus1S k
