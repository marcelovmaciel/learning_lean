import init.data.nat.basic
import init.data.int.basic

section
-- * Quantitfiers + Equality
-- *  Universal


--
-- object of type α → Prop. In that case, given x : α, p x denotes the assertion
-- that p holds of x. Similarly, an object r : α → α → Prop denotes a binary
-- relation on α: given x y : α, r x y denotes the assertion that x is related
-- to y.

-- The universal quantifier, ∀ x : α, p x is supposed to denote the assertion
-- that “for every x : α, p x” holds. As with the propositional connectives, in
-- systems of natural deduction, “forall” is governed by an introduction and
-- elimination rule. Informally, the introduction rule states:

-- Given a proof of p x, in a context where x : α is arbitrary, we obtain a proof ∀ x : α, p x.

-- The elimination rule states:

--   Given a proof ∀ x : α, p x and any term t : α, we obtain a proof of p t.


variables (α : Type*) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
assume h : ∀ x : α, p x ∧ q x,
assume y : α,
show p y, from (h y).left

-- INTRODUCTION AND ELIMINATION

--The canonical way to prove ∀ y : α, p y is to take an arbitrary y, and prove p
-- y. This is the introduction rule. Now, given that h has type ∀ x : α, p x ∧ q
-- x, the expression h y has type p y ∧ q y. This is the elimination rule.

-- TWO WAYS OF PROVING TRANSITIVITY
variables (r : α → α → Prop)
variable  trans_r : ∀ x y z, r x y → r y z → r x z

variables a b c : α
variables (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc


-- NOTe THE IMPLICIT ∀ {x y z} !!!!!!!
variable  trans_r2 : ∀ {x y z}, r x y → r y z → r x z
variables (a2 b2 c2 : α)
variables (hab2 : r a2 b2) (hbc2 : r b2 c2)

#check trans_r2
#check trans_r2 hab2
#check trans_r2 hab2 hbc2


variable refl_r : ∀ x, r x x
variable symm_r : ∀ {x y}, r x y → r y x


example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) :
  r a d :=
trans_r2 (trans_r2 hab (symm_r hcb)) hcd

-- BIG BRAIN THING THAT I DONT UNDERSTAND

--  The impredicativity of Prop means that we can form propositions that
--  quantify over α → Prop. In particular, we can define predicates on α by
--  quantifying over all predicates on α, which is exactly the type of
--  circularity that was once considered problematic.

-- * Equality

-- ** eq.refl _
variables (β : Type*)

example (f : α → β) (a : α) : (λ x, f x) a = f a := eq.refl _
example (a : α) (b : α) : (a, b).1 = a := eq.refl _
example : 2 + 3 = 5 := eq.refl _

-- **  refl
example (f : α → β) (a : α) : (λ x, f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
-- **   eq.subst h1 h2. or h1 ▸ h2
example (α : Type*) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
eq.subst h1 h2

example (α : Type*) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b := h1 ▸ h2

-- ** congr_arg, conrg_fun, congr

-- Specifically, congr_arg can be used to replace the argument, congr_fun can be
-- used to replace the term that is being applied, and congr can be used to
-- replace both at once.

variables a3 b3 : α
variables f g : α → ℕ
variable h₁ : a3 = b3
variable h₂ : f = g

example : f a3 = f b3 := congr_arg f h₁
example : f a3 = g a3 := congr_fun h₂ a3
example : f a3 = g b3 := congr h₂ h₁
-- ** useful identities in standard library

-- import data.int.basic
-- variables a4 b4 c4 d : ℤ

-- example : a4 + 0 = a4 := add_zero a4
-- example : 0 + a4 = a4 := zero_add a4
-- example : a4 * 1 = a4 := mul_one a4
-- example : 1 * a4 = a4 := one_mul a4
-- example : -a4 + a4 = 0 := neg_add_self a4
-- example : a4 + -a4 = 0 := add_neg_self a4
-- example : a4 - a4 = 0 := sub_self a4
-- example : a4 + b4 = b4 + a4 := add_comm a4 b4
-- example : a4 + b4 + c4 = a4 + (b4 + c4) := add_assoc a4 b4 c4
-- example : a4 * b4 = b4 * a4 := mul_comm a4 b4
-- example : a4 * b4 * c4 = a4 * (b4 * c4) := mul_assoc a4 b4 c4
-- example : a4 * (b4 + c4) = a * b4 + a4 * c4 := mul_add a4 b4 c4
-- example : a4 * (b4 + c4) = a4 * b4 + a4 * c4 := left_distrib a4 b4 c4
-- example : (a4 + b4) * c4 = a4 * c4 + b4 * c4 := add_mul a4 b4 c4
-- example : (a4 + b4) * c4 = a4 * c4 + b4 * c4 := right_distrib a4 b4 c4
-- example : a4 * (b4 - c4) = a4 * b4 - a4 * c4 := mul_sub a4 b4 c4
-- example : (a4 - b4) * c4 = a4 * c4 - b4 * c := sub_mul a4

-- no idea why the identifiers are not found
variables x y z : ℤ

example (x y z : ℕ) : x * (y + z) = x * y + x * z :=  mul_add x y z
example (x y z : ℕ) : (x + y) * z = x * z + y * z := add_mul x y z
example (x y z : ℕ) : x + y + z = x + (y + z) := nat.add_assoc x y z

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
  from mul_add (x + y) x y,
have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
  from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm


end

-- *  Calculational proofs
section



variables (a b c d e : ℕ)

variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

theorem T : a = e :=
calc
  a     = b      : h1
    ... = c + 1  : h2
    ... = d + 1  : congr_arg _ h3
    ... = 1 + d  : nat.add_comm d (1 : ℕ)
    ... =  e     : eq.symm h4


-- Beautiful equational proofs;

-- it is not always clear what the names in rw h1 refer to (though, in this
-- case, it is). For that reason, section variables and variables that only
-- appear in a tactic command or block are not automatically added to the
-- context. The include command takes care of that.

include h1 h2 h3 h4

theorem T2 : a = e :=
calc
  a     = b      : by rw h1
    ... = c + 1  : by rw h2
    ... = d + 1  : by rw h3
    ... = 1 + d  : by rw nat.add_comm
    ... =  e     : by rw h4

-- Equivalently

theorem T3 : a = e :=
calc
  a     = d + 1  : by rw [h1, h2, h3]
    ... = 1 + d  : by rw nat.add_comm
    ... = e      : by rw h4


-- simp tactic The simp tactic, instead, rewrites the goal by applying the given
-- identities repeatedly, in any order, anywhere they are applicable in a term.
-- It also uses other rules that have been previously declared to the system,
-- and applies commutativity wisely to avoid looping. As a result, we can also
-- prove the theorem as follows:

theorem T4 : a = e :=
by simp [h1, h2, h3, h4, nat.add_comm]

end

-- The calc command can be configured for any relation that supports some form
-- of transitivity. It can even combine different relations.

section

theorem T5 (a b c d : ℕ)
  (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
calc
  a     = b     : h1
    ... < b + 1 : nat.lt_succ_self b
    ... ≤ c + 1 : nat.succ_le_succ h2
    ... < d     : h3

end

-- ** Proving stuff from previous section using calculational style
-- obviouly mul_add is not found messing up with the proof lol

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
calc
  (x + y) * (x + y) = (x + y) * x + (x + y) * y  : by rw mul_add
    ... = x * x + y * x + (x + y) * y            : by rw add_mul
    ... = x * x + y * x + (x * y + y * y)        : by rw add_mul
    ... = x * x + y * x + x * y + y * y          : by rw ←add_assoc


example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by rw [mul_add, add_mul, add_mul, ←add_assoc]

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by simp [mul_add, add_mul, add_assoc, add_left_comm]

-- * Existential
-- ** Introduction : exists intro

-- The introduction rule is straightforward: to prove ∃ x : α, p x, it suffices
-- to provide a suitable term t and a proof of p t. here are some examples:


open nat

example : ∃ x : ℕ, x > 0 :=
have h : 1 > 0, from zero_lt_succ 0,
exists.intro 1 h

example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
exists.intro 0 h

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z :=
exists.intro y (and.intro hxy hyz)

#check @exists.intro

-- *** ⟨ ⟩ as anonymous constructor for exists
-- We can use the anonymous constructor notation ⟨t, h⟩ for exists.intro t h,
-- when the type is clear from the context.

example : ∃ x : ℕ, x > 0 :=
⟨1, zero_lt_succ 0⟩

example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
⟨0, h⟩

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z := ⟨y, hxy, hyz⟩
-- ** Elimination : exists.elim

-- The existential elimination rule, exists.elim allows us to prove a
-- proposition q from ∃ x : α, p x, by showing that q follows from p w for an
-- arbitrary value w. Roughly speaking, since we know there is an x satisfying p
-- x, we can give it a name, say, w. If q does not mention w, then showing that
-- q follows from p w is tantamount to showing the q follows from the existence
-- of any such x.


variables (α : Type*) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
  (assume w,
    assume hw : p w ∧ q w,
    show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

-- ↑↑↑ in the above example we first elim the first ∃
-- by naming it w, then we prove the goal of form ∃
-- by exists.introing it !
-- So we actually had to assume the var in which the ∃ works
-- together the proposition of interest.
-- Then we used to instantiated variables to construct
-- the new goal, which in this examples also happens to be of
-- the form ∃.


-- *** existential elimination with match

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hw⟩ :=
  ⟨w, hw.right, hw.left⟩
end


-- alternatively,
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hpw, hqw⟩ :=
  ⟨w, hqw, hpw⟩
end
-- or even,

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩


-- *** constructivism and or

-- Just as the constructive “or” is stronger than the classical “or,” so, too,
-- is the constructive “exists” stronger than the classical “exists”. For
-- example, the following implication requires classical reasoning because, from
-- a constructive standpoint, knowing that it is not the case that every x
-- satisfies ¬ p is not the same as having a particular x that satisfies p.

open classical

-- Too tricky, gotta study this
example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
by_contradiction
  (assume h1 : ¬ ∃ x, p x,
    have h2 : ∀ x, ¬ p x, from
      assume x,
      assume h3 : p x,
      have h4 : ∃ x, p x, from  ⟨x, h3⟩,
      show false, from h1 h4,
    show false, from h h2)


variable r : Prop

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
-- * More on the proof language
-- ** The anonymous have + this


-- To start with, we can use anonymous “have” expressions to introduce an
-- auxiliary goal without having to label it. We can refer to the last
-- expression introduced in this way using the keyword this:


variable f : ℕ → ℕ
variable h : ∀ x : ℕ, f x ≤ f (x + 1)

example : f 0 ≤ f 3 :=
have f 0 ≤ f 1, from h 0,
have f 0 ≤ f 2, from le_trans this (h 1),
show f 0 ≤ f 3, from le_trans this (h 2)


-- ** assumption tactic

-- When the goal can be inferred, we can also ask Lean instead to fill in the
-- proof by writing by assumption:This tells Lean to use the assumption tactic,
-- which, in turn, proves the goal by finding a suitable hypothesis in the local
-- context.


example : f 0 ≤ f 3 :=
have f 0 ≤ f 1, from h 0,
have f 0 ≤ f 2, from le_trans (by assumption) (h 1),
show f 0 ≤ f 3, from le_trans (by assumption) (h 2)


-- We can also ask Lean to fill in the proof by writing ‹p›, where p is the proposition whose proof we want Lean to find in the context.You can type these corner quotes using \f< and \f>, respectively. This approach is more robust than using by assumption, because the type of the assumption that needs to be inferred is given explicitly. It also makes proofs more readable.

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
assume : f 0 ≥ f 1,
assume : f 1 ≥ f 2,
have f 0 ≥ f 2, from le_trans this ‹f 0 ≥ f 1›,
have f 0 ≤ f 2, from le_trans (h 0) (h 1),
show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›

example : f 0 ≤ f 3 :=
have f 0 ≤ f 1, from h 0,
have f 1 ≤ f 2, from h 1,
have f 2 ≤ f 3, from h 2,
show f 0 ≤ f 3, from le_trans ‹f 0 ≤ f 1›
  (le_trans ‹f 1 ≤ f 2› ‹f 2 ≤ f 3›)
-- ** anonynomous assume

-- We can also assume a hypothesis without giving it a label:In contrast to the usage with have, an anonymous assume needs an extra colon. The reason is that Lean allows us to write assume h to introduce a hypothesis without specifying it, and without the colon it would be ambiguous as to whether the h here is meant as the label or the assumption. As with the anonymous have, when you use an anonymous assume to introduce an assumption, that assumption can also be invoked later in the proof by enclosing it in French quotes.


example : f 0 ≥ f 1 → f 0 = f 1 :=
assume : f 0 ≥ f 1,
show f 0 = f 1, from le_antisymm (h 0) this

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
assume : f 0 ≥ f 1,
assume : f 1 ≥ f 2,
have f 0 ≥ f 2, from le_trans ‹f 2 ≤ f 1› ‹f 1 ≤ f 0›,
have f 0 ≤ f 2, from le_trans (h 0) (h 1),
show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›
