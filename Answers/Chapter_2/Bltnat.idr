
module Bltnat

howdy : Nat
howdy = 25

public export
beq_nat : Nat -> Nat -> Bool
beq_nat Z Z = True
beq_nat Z (S k) = False
beq_nat (S k) Z = False
beq_nat (S k) (S j) = beq_nat k j


leb : Nat -> Nat -> Bool
leb Z _ = True
leb (S k) (S j) = leb k j
leb _ _ = False
-- alternate and with better ordering: leb (S k) Z = False

tl1 : leb 2 2 = True
tl1 = Refl
tl2 : leb 2 4 = True
tl2 = Refl
tl3 : leb 2555 1 = False
tl3 = Refl

blt_nat : Nat -> Nat -> Bool
blt_nat k j = case beq_nat k j of
                   False => leb k j
                   True => False

tblt1 : blt_nat 2 2 = False
tblt1 = Refl
tblt2 : blt_nat 2 4 = True
tblt2 = Refl
tblt3 : blt_nat 2342 2 = False
tblt3 = Refl
