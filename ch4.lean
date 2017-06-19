variables (A : Type) (p q : A → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
    iff.intro
        (λ H : ∀ x, p x ∧ q x, and.intro
            (λ x : A, and.elim_left (H x))
            (λ x : A, and.elim_right (H x)))
        (λ H : (∀ x, p x) ∧ (∀ x, q x), 
            (λ x : A, and.intro ((and.elim_left H) x) ((and.elim_right H) x)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    (λ H1 : (∀ x, p x → q x), 
        (λ H2 : (∀ x, p x), 
            (λ x : A, (H1 x) (H2 x))))
            
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
    (λ H : (∀ x, p x) ∨ (∀ x, q x),
        (λ x : A, or.elim H
            (λ h : (∀ x, p x), or.inl (h x))
            (λ h : (∀ x, q x), or.inr (h x))))

open classical
variable r : Prop
variable a : A

example : A → ((∀ x : A, r) ↔ r) :=
    (λ x : A, iff.intro
        (λ H : (∀ x : A, r), H x)
        (λ Hr : r, (λ x : A, Hr)))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    iff.intro
        (λ H : (∀ x, p x ∨ r), or.elim (em r)
            (λ Hr : r, or.inr Hr)
            (λ Hnr : ¬r, or.inl
                (λ x : A, or.elim (H x)
                    (λ h : p x, h)
                    (λ Hr : r, absurd Hr Hnr))))
        (λ H : (∀ x, p x) ∨ r,
            (λ x : A, or.elim H
                (λ h : (∀ x, p x), or.inl (h x))
                (λ Hr : r, or.inr Hr)))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    iff.intro
        (λ H : (∀ x, r → p x),
            (λ Hr : r,
                (λ x : A, (H x) Hr)))
        (λ H : (r → ∀ x, p x),
            (λ x : A,
                (λ Hr : r, (H Hr) x)))

variables (men : Type) (barber : men) (shaves : men → men → Prop)

example (H : ∀ x : men, shaves barber x ↔ ¬shaves x x) : false :=
    let Hn := (λ h : shaves barber barber, (iff.elim_left(H barber) h) h) in
    Hn (iff.elim_right(H barber) Hn)

open classical

example : (∃ x : A, r) → r :=
    assume H : (∃ x : A, r),
    obtain (w : A) (Hr : r), from H,
    Hr

example : r → (∃ x : A, r) :=
    assume Hr : r,
    exists.intro a Hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    iff.intro
        (assume H : (∃ x, p x ∧ r),
            and.intro
                (obtain w px_r, from H,
                    exists.intro w (and.elim_left px_r))
                (obtain w px_r, from H,
                    and.elim_right px_r))
        (assume H : (∃ x, p x) ∧ r,
            have Hr : r, from and.elim_right H,
            obtain w px, from and.elim_left H,
            exists.intro w (and.intro px Hr))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
        (assume H : (∃ x, p x ∨ q x),
            obtain w pw_qw, from H,
            or.elim pw_qw
                (assume Hp : p w, or.inl (exists.intro w Hp))
                (assume Hq : q w, or.inr (exists.intro w Hq)))
        (assume H : (∃ x, p x) ∨ (∃ x, q x),
            or.elim H
                (assume H : (∃ x, p x),
                    obtain w pw, from H,
                    exists.intro w (or.inl pw))
                (assume H : (∃ x, q x),
                    obtain w qw, from H,
                    exists.intro w (or.inr qw)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    iff.intro
        (assume H : (∀ x, p x),
            assume H1 : (∃ x, ¬ p x),
                obtain w npw, from H1,
                npw (H w))
        (assume H : ¬ (∃ x, ¬ p x),
            take x,
            or.elim (em (p x))
                (assume Hp : p x, Hp)
                (assume Hnp : ¬ p x, absurd (exists.intro x Hnp) H))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    iff.intro
        (assume H : (∃ x, p x),
            assume H1 : (∀ x, ¬ p x),
                obtain w pw, from H,
                (H1 w) pw)
        (assume H : ¬ (∀ x, ¬ p x),
            by_contradiction
            (assume H1 : ¬ (∃ x, p x),
                H (take x,
                or.elim (em (p x))
                    (assume px : p x, absurd (exists.intro x px) H1)
                    (assume pnx : ¬ (p x), pnx))))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    iff.intro
        (assume H : (¬ ∃ x, p x),
            take x,
            (λ px : p x, H (exists.intro x px)))
        (assume H : ∀ x, ¬ p x,
            (λ H1 : (∃ x, p x),
                obtain w pw, from H1,
                (H w) pw))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    iff.intro
        (assume H : (¬ ∀ x, p x),
            by_contradiction
            (assume H1 : ¬(∃ x, ¬ p x),
                H (take x,
                or.elim (em (p x))
                    (λ px : p x, px)
                    (λ pnx : ¬ p x, absurd (exists.intro x pnx) H1))))
        (assume H : (∃ x, ¬ p x),
            obtain w pnw, from H,
            (assume H: (∀ x, p x),
                 pnw (H w)))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    iff.intro
        (assume H : (∀ x, p x → r),
            assume H1 : (∃ x, p x),
                obtain w pw, from H1,
                (H w) pw)
        (assume H : (∃ x, p x) → r,
            take x,
            (λ px : p x, H (exists.intro x px)))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    iff.intro
        (assume H : (∃ x, p x → r),
            (assume H1 : (∀ x, p x),
                obtain w pw_r, from H,
                pw_r (H1 w)))
        (assume H : (∀ x, p x) → r,
            by_cases
                (assume Hap : (∀ x, p x), exists.intro a (λ pa : p a, H Hap))
                (assume Hnap : ¬(∀ x, p x),
                    by_contradiction
                    (assume Hnex : ¬(∃ x, p x → r),
                        have Hap : (∀ x, p x), from
                            take x,
                            by_contradiction
                            (assume Hnpx : ¬ p x,
                                Hnex (exists.intro x (λ Hpx : p x, absurd Hpx Hnpx))),
                        Hnap Hap)))

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    iff.intro
        (assume H : (∃ x, r → p x),
            assume Hr : r,
                obtain w r_pw, from H,
                exists.intro w (r_pw Hr))
        (assume H : (r → ∃ x, p x),
            by_cases
            (λ Hr : r,
                obtain w pw, from H Hr,
                exists.intro w (λ Hr : r, pw))
            (λ Hnr : ¬ r,
                exists.intro a (λ Hr : r, absurd Hr Hnr)))
