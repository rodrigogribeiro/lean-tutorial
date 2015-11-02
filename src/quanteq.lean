import data.nat

variables (A : Type) (p q : A → Prop)

example : (∀ x : A, p x ∧ q x) → ∀ y : A, p y :=
  assume H : ∀ x : A, p x ∧ q x,
    take y : A,
    show p y, from and.left (H y)

variables (a b c d : A)
premises (Hab : a = b)(Hbc : b = c)(Hcd : c = d)

open eq
open eq.ops

example : a = d := Hab ⬝ Hbc ⬝ Hcd
                    
open nat

example : 2 + 3 = 5 := refl _
example : 2 + 2 = 4 := rfl

example (H1 : a = b)(H2 : p a) : p b := H1 ▸ H2


example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y   : mul.left_distrib
    ...               = x * x + y * x + (x + y) * y : mul.right_distrib
    ...               = x * x + y * x + (x * y + y * y) : mul.right_distrib
    ...               = x * x + y * x + x * y + y * y : add.assoc
    

