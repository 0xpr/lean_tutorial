import data.nat
open nat decidable algebra

definition bex (n : nat) (P : nat → Prop) : Prop :=
    ∃ x : nat, x < n ∧ P x

definition not_bex_zero (P : nat → Prop) : ¬ bex 0 P :=
    (assume H: bex 0 P, 
        exists.elim H
            (take x,
                (assume H' : x < 0 ∧ P x,
                    have H_le_0 : x < 0, from and.elim_left H',
                    or.elim (eq_zero_or_pos x) 
                        (λ H : x = 0, (ne_of_lt H_le_0) H)
                        (λ H : x > 0, (lt.asymm H_le_0) H))))
                
variables {n : nat} {P : nat → Prop}

definition bex_succ (H : bex n P) : bex (succ n) P :=
    exists.elim H 
        (take x, 
            (assume H : x < n ∧ P x,
                have H' : x < n, from and.elim_left H,
                have Hsucc : x < succ n, from lt.trans H' (nat.lt_succ_self n),
                exists.intro x (and.intro Hsucc (and.elim_right H))))

definition bex_succ_of_pred  (H : P n) : bex (succ n) P :=
    exists.intro n (and.intro (nat.lt_succ_self n) H)

definition not_bex_succ (H_1 : ¬ bex n P) (H_2 : ¬ P n) : ¬ bex (succ n) P :=
    (assume H : bex (succ n) P,
        exists.elim H
            (take x, 
                (assume H' : x < succ n ∧ P x, 
                    have H_le : x < succ n, from and.elim_left H',
                    have H_px : P x, from and.elim_right H',
                    or.elim (lt_or_eq_of_le (le_of_lt_succ H_le)) 
                        (λ H : x < n, H_1 (exists.intro x (and.intro H H_px)))
                        (λ H_eq : x = n, H_2 (eq.rec (and.elim_right H') H_eq)))))

definition dec_bex [instance] (H : decidable_pred P) : Π (n : nat), decidable (bex n P)
    | dec_bex 0         := inr (not_bex_zero P)
    | dec_bex (a + 1)   := 
        match dec_bex a with
        | inl iH := inl (bex_succ iH)
        | inr niH := if h : P a then inl (bex_succ_of_pred h) else inr (not_bex_succ niH h)
        end
