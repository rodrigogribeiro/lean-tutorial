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

theorem example3 : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
   iff.intro
       (assume H : p ∧ (q ∨ r), 
          have Hp : p, from and.left H,
          or.elim (and.right H)
                  (assume Hq : q, 
                     show (p ∧ q) ∨ (p ∧ r), 
                       from or.intro_left (p ∧ r) 
                                          (and.intro Hp Hq))
                  (assume Hr : r, 
                     show (p ∧ q) ∨ (p ∧ r), 
                       from or.intro_right (p ∧ q)
                                           (and.intro Hp Hr)))
       (assume H : (p ∧ q) ∨ (p ∧ r),
          or.elim H
                  (assume Hp : p ∧ q, 
                     show p ∧ (q ∨ r), 
                       from (and.intro (and.left Hp)
                                       (or.intro_left r (and.right Hp))))
                  (assume Hq : p ∧ r, 
                     show p ∧ (q ∨ r), 
                       from (and.intro (and.left Hq)
                                       (or.intro_right q (and.right Hq)))))
