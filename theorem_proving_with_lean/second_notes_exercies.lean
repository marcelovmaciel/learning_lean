variables p q r : Prop

-- * commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := iff.intro
(assume h₁: p ∧ q,
 show q ∧ p, from ⟨h₁.right, h₁.left⟩)
(assume h₂: q ∧ p,
show p ∧ q, from  ⟨h₂.right, h₂.left⟩)

example : p ∨ q ↔ q ∨ p := iff.intro
(assume h1: p ∨ q,
  or.elim h1
    (assume hp : p,
    show q ∨ p, from or.inr hp) -- I do think this is way more readable
    (assume hq : q,
    show q ∨ p, from or.inl hq))
(assume h2: q ∨ p,
  or.elim h2
    (assume hq : q, or.inr hq) -- Than this
    (assume hp : p, or.inl  hp))


-- * associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := iff.intro
(assume h1 :(p ∧ q) ∧ r,
⟨h1.left.left, h1.left.right, h1.right⟩)
(assume h2 : p ∧ (q ∧ r),
⟨⟨h2.left, h2.right.left⟩, h2.right.right⟩)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := iff.intro
(assume h1,
or.elim h1
  (assume hpq,
     or.elim hpq
       (assume hp, or.inl hp)
       (assume hq, or.inr (or.inl hq))) -- that was tricky wtf
  (assume hr, or.inr (or.inr hr)))
(assume h2,
  h2.elim
  (assume hp, or.inl (or.inl hp) )
  (assume hqr, hqr.elim
    (assume hq, or.inl (or.inr hq))
    (assume hr, or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := iff.intro
(assume h1,
  have hp:p, from h1.left,
  h1.right.elim
    (assume hq, or.inl ⟨hp,hq⟩)
    (assume hr, or.inr ⟨hp, hr⟩))
(assume h2, h2.elim
  (assume hpq,
    ⟨hpq.left, or.inl hpq.right⟩)
  (assume hpr, ⟨hpr.left, or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := iff.intro
(assume h1, h1.elim
  (assume hp, ⟨or.inl hp, or.inl hp⟩)
  (assume hqr,⟨or.inr hqr.left, or.inr hqr.right⟩)) --
(assume h2,
  h2.left.elim
    (assume hp, or.inl hp)
    (assume hq,
      h2.right.elim
        (assume hp,or.inl hp )
        (assume hr, or.inr ⟨hq,hr⟩)))
-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro
  (assume h1,
    assume pq,
      h1 pq.left pq.right) -- (assume h1, λ pq, (h1 pq.1 pq.2 )) was my first try.
  (assume h2, assume ifp, assume ifq, h2 ⟨ifp, ifq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (assume h1,
      and.intro   -- this one is very relevant, I had
          (assume hp, h1 (or.inl hp)) -- gotten stuck with the and in the goal!
          (assume hq, h1 (or.inr hq)))
    (assume h2,
      assume porq,
        porq.elim
          (assume hp, h2.left hp)
          (assume hq, h2.right hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume h1,
      and.intro
        (assume hp, h1 (or.inl hp))
        (assume hq, h1 (or.inr hq)))
    (assume h2,
      assume porq,
             porq.elim
               (assume hp, h2.left hp)
               (assume hq, h2.right hq))


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume h1,
  assume h2,
  h1.elim
    (assume notp, notp h2.left)
    (assume notq, notq h2.right)

example : ¬(p ∧ ¬p) :=
  assume h1, absurd h1.left h1.right

example : p ∧ ¬q → ¬(p → q) :=
  assume hp_and_nq,
  assume hp_then_q,
    hp_and_nq.right (hp_then_q hp_and_nq.left)

example : ¬p → (p → q) :=
  assume hnotp,
  assume hp,
    absurd hp hnotp

example : (¬p ∨ q) → (p → q) :=
  assume hnotp_or_q,
  assume hp,
    hnotp_or_q.elim
      (assume hnotp, absurd hp hnotp)
      (assume hq, hq)

example : p ∨ false ↔ p :=
  iff.intro
  (assume hp_or_false, hp_or_false.elim
    (assume hp,hp)
    (assume f, f.elim))
  (assume hp, or.inl hp)

example : p ∧ false ↔ false :=
  iff.intro
  (assume hp_and_false, hp_and_false.right)
  (assume f, f.elim)

example : (p → q) → (¬q → ¬p) :=
  assume hifp_then_q,
  assume hnot_q,
  assume hp,  absurd (hifp_then_q hp) hnot_q
