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
(assume h2, _)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry
