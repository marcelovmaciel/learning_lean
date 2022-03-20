import data.int.basic -- this doesnt work
import data.real.basic -- this doesnt work

open classical

variables (α : Type*) (p q : α → Prop)
variable r : Prop

-- This is dumb, I can't prove this obvious thing without tactics lol
example : (∃ x : α, r) → r :=
assume h,
  exists.elim h
    (assume w,
     assume hw,
            hw)
-- ⇯ I don't truly grokk what is going on here. Just following the syntax lol
-- Another way of doing that is using tactics that
-- I learnt in the number game

-- begin
-- cases h, exact h_h
-- end


example (a : α) : r → (∃ x : α, r) :=
assume h, ⟨a,h⟩



example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
  (assume hl,
  exists.elim hl
  (assume w,
  assume hw,
  ⟨⟨w, hw.left⟩,hw.right ⟩)) --
  (assume hr,
  exists.elim hr.left
    (assume w,
    assume hw,
  ⟨w, hw, hr.right⟩))  --

-- another way of solving
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
(assume hl,
  match hl with ⟨w, hw ⟩ :=
  ⟨⟨w, hw.left⟩, hw.right ⟩
  end)
(assume hr,
  match hr.left with ⟨w, hw⟩ :=
  ⟨w, hw, hr.right⟩
  end)


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
(assume hl,
  exists.elim hl
  (assume w,
  assume hw,
  or.elim hw
  (assume hpw, (or.inl ⟨w, hpw⟩))
  (assume hqw,(or.inr ⟨w, hqw⟩))))
(assume hr, _)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry






-- *    Prove these equivalences:

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

--  You should also try to understand why the reverse implication is not
--    derivable in the last example. It is often possible to bring a component
--    of a formula outside a universal quantifier, when it does not depend on
--    the quantified variable. Try proving these (one direction of the second of
--    these requires classical logic):


example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

-- Consider the “barber paradox,” that is, the claim that in a certain town
-- there is a (male) barber that shaves all and only the men who do not
-- shave themselves. Prove that this is a contradiction:


variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
false := sorry

--  Remember that, without any parameters, an expression of type Prop is just
--  an assertion. Fill in the definitions of prime and Fermat_prime below,
--  and construct each of the given assertions. For example, you can say that
--  there are infinitely many primes by asserting that for every natural
--  number n, there is a prime number greater than n. Goldbach’s weak
--  conjecture states that every odd number greater than 5 is the sum of
--  three primes. Look up the definition of a Fermat prime or any of the
--  other statements, if necessary.

#check even

def prime (n : ℕ) : Prop := sorry
def infinitely_many_primes : Prop := sorry
def Fermat_prime (n : ℕ) : Prop := sorry
def infinitely_many_Fermat_primes : Prop := sorry
def goldbach_conjecture : Prop := sorry
def Goldbach's_weak_conjecture : Prop := sorry
def Fermat's_last_theorem : Prop := sorry

--  Give a calculational proof of the theorem log_mul below.




variables log exp     : real → real
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

 -- this ensures the assumptions are available in tactic proofs
 include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]
example (y : real) (h : y > 0)  : exp (log y) = y :=
  exp_log_eq h
theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
  sorry

--  Prove the theorem below, using only the ring properties of ℤ enumerated in
--  Section 4.2 and the theorem sub_self.


#check sub_self
example (x : ℤ) : x * 0 = 0 :=
 sorry
