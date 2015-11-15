
inductive weekday : Type :=
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

open weekday

namespace weekday

  local abbreviation cases_on := @weekday.cases_on

  definition number_of_day (d : weekday) : nat := 
    weekday.rec_on d 1 2 3 4 5 6 7

  definition next (d : weekday) : weekday :=
    cases_on d monday tuesday wednesday thursday friday saturday sunday

  definition previous (d : weekday) : weekday := 
    cases_on d saturday sunday monday tuesday wednesday thursday friday

  theorem next_previous (d : weekday) : previous (next d) = d :=
    weekday.induction_on d
            (show next (previous sunday) = sunday, from rfl)
            (show next (previous monday) = monday, from rfl)
            (show next (previous tuesday) = tuesday, from rfl)
            (show next (previous wednesday) = wednesday, from rfl)
            (show next (previous thursday) = thursday, from rfl)
            (show next (previous friday) = friday, from rfl)
            (show next (previous saturday) = saturday, from rfl)
end weekday

namespace structures
  
  structure Semigroup : Type :=
       (carrier : Type)
       (mul : carrier → carrier → carrier)
       (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

end structures


namespace natural 
  inductive natural : Type :=
    | zero : natural
    | succ : natural → natural

  local abbreviation rec_on := @natural.rec_on
  local abbreviation induction_on := @natural.induction_on
  local abbreviation succ := @natural.succ
  open natural

  definition add (n m : natural) : natural :=
    rec_on n m (λ n ac, natural.succ ac)

  notation 0 := @natural.zero
  infix `+` := add

  open eq

  theorem add_zero (n : natural) : n + 0 = n :=
    induction_on n 
      (show 0 + 0 = 0, from rfl)
      (take n, 
       assume IH : (n + 0) = n,
       show ((succ n) + 0) = succ n, from 
         calc
           succ n + 0 = succ (n + 0) : rfl 
           ... = succ n : IH)
end natural
