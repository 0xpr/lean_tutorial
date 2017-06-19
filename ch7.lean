open nat

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)

open vector

notation h :: t := cons h t

-- defining map with only recursors

definition head_aux {A : Type} {m n : nat} (v : vector A m) : (m = succ n) → A :=
  vector.cases_on v
    (assume H : 0 = succ n, nat.no_confusion H)
    (λ c a tv,
      (assume H : succ c = succ n, a))

definition head {A : Type} : Π {n}, vector A (succ n) → A :=
  (λ n v, head_aux v rfl)

definition tail_aux {A : Type} {n m : nat} (v : vector A m) :
      m = succ n → vector A n :=
  vector.cases_on v
    (assume H : 0 = succ n, nat.no_confusion H)
    (take m (a : A) w : vector A m,
      assume H : succ m = succ n,
      have H1 : m = n, from (nat.no_confusion H) (fun e : m = n, e),
      eq.rec_on H1 w)

definition tail {A : Type} {n : nat} (v : vector A (succ n)) : vector A n :=
  tail_aux v rfl

-- defining map without recursors
--  we can use head and tail (the tail example is already covered in the book,
--  so we only have to worry about head)
definition map {A B C : Type} (f : A → B → C)
    : Π {n : nat}, vector A n → vector B n → vector C n :=
  (λ n : nat,
    nat.rec (λ vecA vecB, nil)
      (λ n tf,
        (λ vecA vecB, 
          have ele_a : A, from head vecA,
          have ele_b : B, from head vecB,
          have tl_a : vector A n, from tail vecA,
          have tl_b : vector B n, from tail vecB,
          f ele_a ele_b :: tf tl_a tl_b))
      n)
