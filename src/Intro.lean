import standard
import data.sigma

open nat bool prod sigma

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
          

set_option pp.universes true

constants A B C : Type

check prod
check prod A 
check prod A B


eval ((λ x : nat, x + 1) 1) -- result 2


definition gfa (f : A → B)(g : B → C)(x : A) : C := g (f x)

print gfa


section composition
  variables (A B C : Type)
  variables (f : A -> B) (g : B -> C) (x : A)

  definition comp := g (f x)
end composition
 
namespace hide
  constant list : Type -> Type
  constant cons : Π A : Type, A -> list A -> list A
  constant nil : Π A : Type, list A
end hide


namespace prodsamples 
  variable A : Type
  variable B : A -> Type
  variable a : A
  variable b : B a
  
  check ⟨ a , b ⟩

  eval pr1 ⟨ a , b ⟩

  definition id {A : Type} : A -> A := λ x , x
end prodsamples
