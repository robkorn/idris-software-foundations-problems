
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

-- Exercise 9.1
andbTelim2_rhs_1 : (prf : andb False c = True) -> c = True
andbTelim2_rhs_1 prf = ?andbTelim2_rhs_1_rhs

andbTelim2 : (b, c : Bool) -> (andb b c = True) -> c = True
andbTelim2 False c prf = andbTelim2_rhs_1 prf
andbTelim2 True c prf = ?andbTelim2_rhs_2
