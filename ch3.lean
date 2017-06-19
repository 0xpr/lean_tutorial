open classical
variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  iff.intro
    (assume H : p ∧ q,
      show q ∧ p, from and.intro (and.elim_right H) (and.elim_left H))
    (assume H : q ∧ p,
      show p ∧ q, from and.intro (and.elim_right H) (and.elim_left H))
        
example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (assume H : p ∨ q, show q ∨ p, from
        or.elim H
          (assume H : p, show q ∨ p, from or.intro_right q H)
          (assume H : q, show q ∨ p, from or.intro_left p H))
    (assume H : q ∨ p, show p ∨ q, from
        or.elim H
          (assume H : q, show p ∨ q, from or.intro_right p H)
          (assume H : p, show p ∨ q, from or.intro_left q H))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume H : (p ∧ q) ∧ r, show p ∧ (q ∧ r), from
      and.intro
        (and.elim_left (and.elim_left H))
        (and.intro (and.elim_right (and.elim_left H)) (and.elim_right H)))
    (assume H : p ∧ (q ∧ r), show (p ∧ q) ∧ r, from
      and.intro
        (and.intro (and.elim_left H) (and.elim_left (and.elim_right H)))
        (and.elim_right (and.elim_right H)))
    
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume H : (p ∨ q) ∨ r, show p ∨ (q ∨ r), from
      or.elim H
        (assume H : p ∨ q, show p ∨ (q ∨ r), from
          or.elim H
          (assume H : p, show p ∨ (q ∨ r), from
            or.intro_left (q ∨ r) H)
          (assume H : q, show p ∨ (q ∨ r), from
            or.intro_right p (or.intro_left r H)))
        (assume H : r, show p ∨ (q ∨ r), from
          or.intro_right p (or.intro_right q H)))
    (assume H : p ∨ (q ∨ r), show (p ∨ q) ∨ r, from
      or.elim H
        (assume H : p, show (p ∨ q) ∨ r, from
          or.intro_left r (or.intro_left q H))
        (assume H : q ∨ r, show (p ∨ q) ∨ r, from
          or.elim H
          (assume H : q, show (p ∨ q) ∨ r, from
            or.intro_left r (or.intro_right p H))
          (assume H : r, show (p ∨ q) ∨ r, from
            or.intro_right (p ∨ q) H)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume H : p ∧ (q ∨ r), show (p ∧ q) ∨ (p ∧ r), from
      have Hp : p, from and.elim_left H,
      or.elim (and.elim_right H)
        (assume Hq : q, show (p ∧ q) ∨ (p ∧ r), from
          or.intro_left (p ∧ r) (and.intro Hp Hq))
        (assume Hr : r, show (p ∧ q) ∨ (p ∧ r), from
          or.intro_right (p ∧ q) (and.intro Hp Hr)))
    (assume H : (p ∧ q) ∨ (p ∧ r), show p ∧ (q ∨ r), from
      or.elim H
        (assume H : p ∧ q, show p ∧ (q ∨ r), from
          and.intro (and.elim_left H)
                    (or.intro_left r (and.elim_right H)))
        (assume H : p ∧ r, show p ∧ (q ∨ r), from
          and.intro (and.elim_left H)
                    (or.intro_right q (and.elim_right H))))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume H : p ∨ (q ∧ r), show (p ∨ q) ∧ (p ∨ r), from
      or.elim H
        (assume Hp : p, show (p ∨ q) ∧ (p ∨ r), from
          and.intro (or.intro_left q Hp) (or.intro_left r Hp))
        (assume Hqr : q ∧ r, show (p ∨ q) ∧ (p ∨ r), from
          and.intro (or.intro_right p (and.elim_left Hqr))
                    (or.intro_right p (and.elim_right Hqr))))
    (assume H : (p ∨ q) ∧ (p ∨ r), show p ∨ (q ∧ r), from
      (λ Hpq : p ∨ q,
        or.elim Hpq
          (λ Hp : p,
            λ Hpr : p ∨ r, or.inl Hp)
          (λ Hq : q,
            (λ Hpr : p ∨ r, 
              or.elim Hpr
                (λ Hp : p, or.inl Hp)
                (λ Hr : r, or.inr (and.intro Hq Hr)))))
      (and.elim_left H)
      (and.elim_right H))


-- other properties

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro
    (assume H : p → (q → r), show (p ∧ q → r), from
      (assume Hpq : p ∧ q, show r, from
        (H (and.elim_left Hpq)) (and.elim_right Hpq)))
    (assume H : p ∧ q → r, show  p → (q → r), from
      (assume Hp : p, show q → r, from
        (assume Hq : q, show r, from
          H (and.intro Hp Hq))))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (λ H : (p ∨ q) → r,
      and.intro (λ Hp : p, H (or.inl Hp)) (λ Hq : q, H (or.inr Hq)))
    (λ H : (p → r) ∧ (q → r),
      (λ Hpq : p ∨ q,
        or.elim Hpq
          (λ Hp : p, (and.elim_left H) Hp)
          (λ Hq : q, (and.elim_right H) Hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (λ H : ¬(p ∨ q), and.intro
      (λ Hp : p, H (or.inl Hp))
      (λ Hq : q, H (or.inr Hq)))
    (λ H : ¬p ∧ ¬q,
      (λ Hpq : p ∨ q, or.elim Hpq
        (λ Hp : p, (and.elim_left H) Hp)
        (λ Hq : q, (and.elim_right H) Hq)))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (λ H : ¬p ∨ ¬q, or.elim H
    (λ Hp : ¬p,
      (λ Hpq : p ∧ q, Hp (and.elim_left Hpq)))
    (λ Hq : ¬q,
      (λ Hpq : p ∧ q, Hq (and.elim_right Hpq))))
      
example : ¬(p ∧ ¬ p) :=
  (λ H : p ∧ ¬ p, (and.elim_right H) (and.elim_left H))
  
example : p ∧ ¬q → ¬(p → q) :=
  (λ H : p ∧ ¬q,
    (λ H1 : p → q,
      (and.elim_right H) (H1 (and.elim_left H))))

example : ¬p → (p → q) :=
  (λ Hnp : ¬p,
    (λ Hp : p, false.elim (Hnp Hp)))

example : (¬p ∨ q) → (p → q) :=
  (λ H : ¬p ∨ q, or.elim H
    (λ Hnp : ¬p, (λ Hp : p, false.elim (Hnp Hp)))
    (λ Hq : q, (λ Hp : p, Hq)))

example : p ∨ false ↔ p :=
  iff.intro
    (λ H : p ∨ false, or.elim H
      (λ Hp : p, Hp)
      (λ H : false, false.elim H))
    (λ Hp : p, or.inl Hp)

example : p ∧ false ↔ false :=
  iff.intro
    (λ H : p ∧ false, and.elim_right H)
    (λ H : false, false.elim H)

example : ¬(p ↔ ¬p) := iff.elim
  (λ H1 : p → ¬p,
    (λ H2 : ¬p → p,
      let Hnp := (λ Hp : p, (H1 Hp) Hp) in
      let Hp := H2 Hnp in
        Hnp Hp))

example : (p → q) → (¬q → ¬p) :=
  (λ H : p → q,
    (λ Hnq : ¬q,
      (λ Hp : p, Hnq (H Hp))))

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  let or_help (Hnr : ¬r) (H : r ∨ s) :=
    or.elim H
        (λ Hr : r, false.elim (Hnr Hr))
        (λ Hs : s, Hs)
  in
  (λ H : p → r ∨ s,
    let mr := em r in
      or.elim mr
        (λ Hr : r, or.inl (λ Hp : p, Hr))
        (λ Hnr : ¬r, or.inr (λ Hp : p, or_help Hnr (H Hp))))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (λ H : ¬(p ∧ q),
    or.elim (em p)
      (λ Hp : p,  
        or.elim (em q)
          (λ Hq : q, false.elim (H (and.intro Hp Hq)))
          (λ Hnq : ¬q, or.inr Hnq))
      (λ Hnp : ¬p, or.inl Hnp))

example : ¬(p → q) → p ∧ ¬q :=
  (λ H : ¬(p → q),
    let Hnq := (λ Hq : q, H (λ Hp : p, Hq)) in
    let Hp := or.elim (em p)
      (λ Hp : p, Hp)
      (λ Hnp : ¬p, false.elim (H (λ Hp : p, false.elim (Hnp Hp))))
    in
    and.intro Hp Hnq)

example : (p → q) → (¬p ∨ q) :=
  (λ H : p → q,
    or.elim (em p)
      (λ Hp : p, or.inr (H Hp))
      (λ Hnp : ¬p, or.inl Hnp))

example : (¬q → ¬p) → (p → q) :=
  (λ H : ¬q → ¬p,
    (λ Hp : p, or.elim (em q)
      (λ Hq : q, Hq)
      (λ Hnq : ¬q, false.elim ((H Hnq) Hp))))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  (λ H : (p → q) → p,
    or.elim (em p)
      (λ Hp : p, Hp)
      (λ Hnp : ¬p, H
        (λ Hp : p, false.elim (Hnp Hp))))
