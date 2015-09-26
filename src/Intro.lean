import standard

open nat bool

check 3

check tt


-- some logic using lean

theorem and_commutative(p q:Prop) : p ∧ q → q ∧ p:=
  assume Hpq : p ∧ q,
    have Hp : p, from and.elim_left Hpq,
    have Hq : q, from and.elim_right Hpq,
  show q ∧ p, from and.intro Hq Hp

theorem implies_chain (p q r : Prop) : (p → q) → (q → r) → (p → r) :=
  assume Hpq : p → q,
  assume Hqr : q → r,
  assume Hp : p,
  show r, from Hqr (Hpq Hp)
          
