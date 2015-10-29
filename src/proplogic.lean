open classical


variables p q r s : Prop

theorem example1 : p ∧ q ↔ q ∧ p :=
    iff.intro 
      (assume Hpq : p ∧ q, 
        show q ∧ p, from and.intro (and.right Hpq) 
                                   (and.left Hpq))
      (assume Hqp : q ∧ p, 
        show p ∧ q, from and.intro (and.right Hqp)
                                   (and.left Hqp))
    
    
theorem example2 : p ∨ q ↔ q ∨ p :=
    iff.intro
      (assume Hpq : p ∨ q, 
          or.elim Hpq
            (assume Hp : p,
              show q ∨ p, from or.intro_right q Hp)
            (assume Hq : q,
              show q ∨ p, from or.intro_left p Hq))
      (assume Hqp : q ∨ p,
          or.elim Hqp 
            (assume Hq : q, 
              show p ∨ q, from or.intro_right p Hq)
            (assume Hp : p,
              show p ∨ q, from or.intro_left q Hp))
       
