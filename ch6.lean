namespace hide

inductive nat : Type :=
| zero : nat
| succ : nat → nat

namespace nat

definition add (m n : nat) : nat :=
nat.rec_on n m (fun n add_m_n, succ add_m_n)

notation 0 := zero
infix `+` := add

theorem add_zero (m : nat) : m + 0 = m := rfl

theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl

local abbreviation induction_on := @nat.induction_on

theorem zero_add (n : nat) : 0 + n = n :=
induction_on n
  (show 0 + 0 = 0, from rfl)
  (take n,
    assume IH : 0 + n = n,
    show 0 + succ n = succ n, from
      calc
        0 + succ n = succ (0 + n) : rfl
          ... = succ n : IH)

attribute add [reducible]
theorem add_assoc (m n k : nat) : m + n + k = m + (n + k) :=
induction_on k rfl (take k IH, eq.subst IH rfl)

theorem succ_add (m n : nat) : succ m + n = succ (m + n) :=
induction_on n
  (show succ m + 0 = succ (m + 0), from rfl)
  (take n,
    assume IH : succ m + n = succ (m + n),
    show succ m + succ n = succ (m + succ n), from
      calc
        succ m + succ n = succ (succ m + n) : rfl
          ... = succ (succ (m + n)) : IH
          ... = succ (m + succ n) : rfl)

theorem add_comm (m n : nat) : m + n = n + m :=
induction_on n
  (show m + 0 = 0 + m, from eq.symm (zero_add m))
  (take n,
    assume IH : m + n = n + m,
    calc
      m + succ n = succ (m + n) : rfl
        ... = succ (n + m) : IH
        ... = succ n + m : succ_add)

-- define mul by recursion on the second argument
definition mul (m n : nat) : nat :=
  nat.rec_on n 0 (fun n mul_m_n, mul_m_n + m)

infix `*` := mul

-- these should be proved by rfl
theorem mul_zero (m : nat) : m * 0 = 0 := rfl

theorem mul_succ (m n : nat) : m * (succ n) = m * n + m :=
  induction_on n
    (show m * (succ 0) = m * 0 + m, from rfl)
    (take n,
      assume IH : m * (succ n) = m * n + m,
      calc
        m * (succ (succ n)) = m * (succ n) + m : rfl)

theorem zero_mul (n : nat) : 0 * n = 0 :=
  induction_on n
    (show 0 * 0 = 0, from rfl)
    (take n,
      assume IH : 0 * n = 0,
      calc
        0 * (succ n) = (0 * n) + 0 : rfl
        ... = 0 + 0 : IH
        ... = 0 : rfl)

theorem mul_distrib (m n k : nat) : m * (n + k) = m * n + m * k :=
  induction_on k
    (show m * (n + 0) = m * n + m * 0, from rfl)
    (take k,
      assume IH : m * (n + k) = m * n + m * k,
      calc
        m * (n + (succ k)) = m * succ (n + k) : rfl
        ... = m * (n + k) + m : mul_succ
        ... = (m * n + m * k) + m : IH
        ... = m * n + (m * k + m) : add_assoc
        ... = m * n + m * (succ k) : mul_succ)

theorem mul_assoc (m n k : nat) : m * n * k = m * (n * k) :=
  induction_on k 
    rfl
    (take k,
      assume IH : m * n * k = m * (n * k),
        calc
          m * n * succ k = m * n * k + m * n : mul_succ
          ... = m * (n * k) + m * n : IH
          ... = m * (n * k + n) : mul_distrib
          ... = m * (n * succ k) : mul_succ)

-- hint: you will need to prove an auxiliary statement
theorem succ_mul (m n : nat) : succ m * n = m * n + n :=
  induction_on n
    rfl
    (take n,
      assume IH : succ m * n = m * n + n,
        calc
          succ m * succ n = succ m * n + succ m : mul_succ
          ... = (m * n + n) + succ m : IH
          ... = m * n + (n + succ m) : add_assoc
          ... = m * n + succ (n + m) : add_succ
          ... = m * n + (succ n + m) : succ_add
          ... = m * n + (m + succ n) : add_comm
          ... = (m * n + m) + succ n : add_assoc
          ... = m * succ n + succ n : mul_succ)

theorem mul_comm (m n : nat) : m * n = n * m :=
  induction_on n
    (show m * 0 = 0 * m, from
      calc 
        m * 0 = 0 : mul_zero
        ... = 0 * m : zero_mul)
    (take n,
      assume IH : m * n = n * m,
      calc
        m * succ n = m * n + m : mul_succ
        ... = n * m + m : IH
        ... = succ n * m : succ_mul)

definition pred (n : nat) : nat := nat.cases_on n zero (fun n, n)

theorem pred_succ (n : nat) : pred (succ n) = n := rfl

theorem succ_pred (n : nat) : n ≠ 0 → succ (pred n) = n :=
  nat.rec_on n
    (λ H : 0 ≠ 0,
      have H' : 0 = 0, from rfl,
      absurd H' H)
    (take n,
      assume IH : n ≠ 0 → succ (pred n) = n,
        (λ H : succ n ≠ 0,
          calc
            succ (pred (succ n)) = succ n : rfl))


end nat

end hide

namespace hide

inductive list (A : Type) : Type :=
| nil {} : list A
| cons : A → list A → list A

namespace list

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

variable {A : Type}

notation h :: t  := cons h t

definition append (s t : list A) : list A :=
list.rec_on s t (λ x l u, x::u)

notation s ++ t := append s t

theorem nil_append (t : list A) : nil ++ t = t := rfl

theorem cons_append (x : A) (s t : list A) : x::s ++ t = x::(s ++ t) := rfl

theorem append_nil (t : list A) : t ++ nil = t :=
  list.induction_on t
    rfl
    (λ x t,
      assume IH : t ++ nil = t,
        calc
          (x :: t) ++ nil = x :: (t ++ nil) : rfl
          ... = x :: t : IH)
        
theorem append_assoc (r s t : list A) : r ++ s ++ t = r ++ (s ++ t) :=
  list.induction_on r
    rfl
    (λ x r,
      assume IH : r ++ s ++ t = r ++ (s ++ t),
        calc
        (x :: r) ++ s ++ t = x :: (r ++ s) ++ t : rfl
        ... = x :: (r ++ s ++ t) : rfl
        ... = x :: (r ++ (s ++ t)) : IH
        ... = (x :: r) ++ (s ++ t) : rfl)

end list
end hide

namespace hide

inductive eq {A : Type} (a : A) : A → Prop :=
  refl : eq a a

theorem cast {A B : Type} (p : eq A B) (a : A) : B :=
  (eq.rec a) p

theorem subst {A : Type} {a b : A} {P : A → Prop}
  (H_1 : eq a b) (H_2 : P a) : P b :=
  (eq.rec H_2) H_1

theorem symm {A : Type} {a b : A} (H : eq a b) : eq b a :=
  (eq.rec (eq.refl a)) H

theorem trans {A : Type} {a b c : A} (H_1 : eq a b) (H_2 : eq b c) : eq a c :=
  eq.rec H_1 H_2

theorem congr {A B : Type} {a b : A} (f : A → B) (H : eq a b) : eq (f a) (f b) :=
  eq.rec (eq.refl (f a)) H

theorem hcongr {A : Type} {B : A → Type} {a b : A} (f : Π x : A, B x)
      (H : eq a b) : eq (eq.rec_on H (f a)) (f b) :=
  have h1 : ∀ h : eq a a, eq (eq.rec_on h (f a)) (f a), from
    (assume h : eq a a, eq.refl (eq.rec_on h (f a))),
  have h2 : ∀ h : eq a b, eq (eq.rec_on h (f a)) (f b), from
    eq.rec_on H h1,
  show eq (eq.rec_on H (f a)) (f b), from
    h2 H

end hide

namespace hide
 
inductive tree (A : Type) : Type :=
| leaf : A → tree A
| node : tree A → tree A → tree A

open tree
 
variable {A : Type}

theorem leaf_ne_node {a : A} {l r : tree A}
    (h : leaf a = node l r) : false :=
  tree.no_confusion h

theorem leaf_inj {a b : A} (h : leaf a = leaf b) : a = b :=
  tree.no_confusion h (fun e : a = b, e)

theorem node_inj_left {l1 r1 l2 r2 : tree A}
    (h : node l1 r1 = node l2 r2) : l1 = l2 :=
  tree.no_confusion h (fun (l : l1 = l2) (r : r1 = r2), l)

theorem node_inj_right {l1 r1 l2 r2 : tree A}
    (h : node l1 r1 = node l2 r2) : r1 = r2 :=
  tree.no_confusion h (fun (l : l1 = l2) (r : r1 = r2), r)
     
end hide
