open classical

--  Proving double negation implies excluded middle

variables p q : Prop

theorem dne {p : Prop} (H : ¬¬p) : p :=
    or.elim (em p)
    (assume Hp : p, Hp)
    (assume Hnp : ¬p, absurd Hnp H)

theorem help3 (negated : ¬(p ∨ ¬p)) : ¬p ∧ ¬¬p :=
    and.intro
        (assume Hp : p, 
            show false, from negated (or.intro_left (¬p) Hp))
        (assume Hp : ¬p,
            show false, from negated (or.intro_right p Hp))

theorem help2 (single_negated : ¬(p ∨ ¬p)) : false :=
    have Hp : ¬p ∧ ¬¬p, from help3 p single_negated,
    show false, from (and.elim_right Hp (and.elim_left Hp))

theorem emm_ : p ∨ ¬p := dne (help2 p)

check emm_ 
