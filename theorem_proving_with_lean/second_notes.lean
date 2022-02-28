-- -- * On propositions ----------------------------------------------------------

-- we can build a small logical system directly in lean
namespace ml
constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant not : Prop → Prop
constant implies : Prop → Prop → Prop

variables p q r : Prop
#check and p q                      -- Prop
#check or (and p q) r               -- Prop
#check implies (and p q) (and q p)  -- Prop

constant Proof : Prop → Type

constant and_comm : Π p q : Prop,
  Proof (implies (and p q) (and q p))

#check and_comm p q      -- Proof (implies (and p q) (and q p))

end ml

-- How do we go from a Proof object to the usual proof using the objects
-- themselves? By conflating Proof p with p! instantiating p is thus tantamount
-- to proving p!


-- Some simplifications are possible, however. To start with, we can avoid
-- writing the term Proof repeatedly by conflating Proof p with p itself. In
-- other words, whenever we have p : Prop, we can interpret p as a type, namely,
-- the type of its proofs. We can then read t : p as the assertion that t is a
-- proof of p. Moreover, once we make this identification, the rules for
-- implication show that we can pass back and forth between implies p q and p →
-- q. In other words, implication between propositions p and q corresponds to
-- having a function that takes any element of p to an element of q. As a
-- result, the introduction of the connective implies is entirely redundant: we
-- can use the usual function space constructor p → q from dependent type theory
-- as our notion of implication.This is the approach followed in the Calculus of
-- Constructions, and hence in Lean as well. The fact that the rules for
-- implication in a proof system for natural deduction correspond exactly to the
-- rules governing abstraction and application for functions is an instance of
-- the Curry-Howard isomorphism, sometimes known as the propositions-as-types
-- paradigm. In fact, the type Prop is syntactic sugar for Sort 0, the very
-- bottom of the type hierarchy described in the last chapter. Moreover, Type u
-- is also just syntactic sugar for Sort (u+1). Prop has some special features,
-- but like the other type universes, it is closed under the arrow constructor:
-- if we have p q : Prop, then p → q : Prop.

-- There are at least two ways of thinking about propositions as types. To some
-- who take a constructive view of logic and mathematics, this is a faithful
-- rendering of what it means to be a proposition: a proposition p represents a
-- sort of data type, namely, a specification of the type of data that
-- constitutes a proof. A proof of p is then simply an object t : p of the right
-- type.


-- They talk about interpretations and so on what matters is the bottom line

-- To formally express a mathematical assertion in the language of dependent
-- type theory, we need to exhibit a term p : Prop. To prove that assertion, we
-- need to exhibit a term t : p. Lean’s task, as a proof assistant, is to help
-- us to construct such a term, t, and to verify that it is well-formed and has
-- the correct type.


-- ** What differs theorem from def?
-- It gives a hint to the compiler!


-- Note that the theorem command is really a version of the definition command:
-- under the propositions and types correspondence, proving the theorem p → q →
-- p is really the same as defining an element of the associated type. To the
-- kernel type checker, there is no difference between the two.

-- There are a few pragmatic differences between definitions and theorems,
-- however. In normal circumstances, it is never necessary to unfold the
-- “definition” of a theorem; by proof irrelevance, any two proofs of that
-- theorem are definitionally equal. Once the proof of a theorem is complete,
-- typically we only need to know that the proof exists; it doesn’t matter what
-- the proof is. In light of that fact, Lean tags proofs as irreducible, which
-- serves as a hint to the parser (more precisely, the elaborator) that there is
-- generally no need to unfold it when processing a file. In fact, Lean is
-- generally able to process and check proofs in parallel, since assessing the
-- correctness of one proof does not require knowing the details of another.


-- The three ways below are equivalent, but some are clearer to read


constants p q : Prop

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

#print t1


theorem t2 : p → q → p :=
assume hp : p,
assume hq : q,
hp

#print t2

theorem t3 : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp

-- assume here looks like the intro tactic
theorem t4 (hp : p) (hq : q) : p := hp
#check t4    -- p → q → p


-- the axiom kw is like constant for Prop
axiom hp : p
theorem t5 : q → p := t4 hp


-- Notice, by the way, that the original theorem t1 is true for any propositions
-- p and q, not just the particular constants declared. So it would be more
-- natural to define the theorem so that it quantifies over those, too:

theorem t6 (p q : Prop) (hp : p) (hq : q) : p := hp
#check t6 -- ∀ (p q : Prop), p → q → p

-- The type of t1 is now ∀ p q : Prop, p → q → p. We can read this as the
-- assertion “for every pair of propositions p q, we have p → q → p.” The symbol
-- ∀ is alternate syntax for Π, and later we will see how Pi types let us model
-- universal quantifiers more generally.

-- If p and q have been declared as variables, Lean will generalize them for us automatically:
variables p q : Prop

theorem t7 : p → q → p := λ (hp : p) (hq : q), hp
#check t7
-- note it is the same damn thing as t6!
variables r s : Prop

#check t7 p q                -- p → q → p
#check t7 r s                -- r → s → r
#check t7 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable h : r → s

#check t7 (r → s) (s → r) h  -- (s → r) → r → s


theorem t8 (h₁ : q → r) (h₂ : p → q) : p → r :=
assume h₃ : p,
show r, from h₁ (h₂ h₃)

-- * Having fun with connectives
#check p → q → p ∧ q
#check ¬p → p ↔ false
#check p ∨ q → q ∨ p


-- The order of operations is as follows: unary negation ¬ binds most strongly,
-- then ∧, then ∨, then →, and finally ↔. For example, a ∧ b → c ∨ d ∧ e means
-- (a ∧ b) → (c ∨ (d ∧ e)).

--In the last chapter we observed that lambda abstraction can be viewed as an
--“introduction rule” for →. In the current setting, it shows how to “introduce”
--or establish an implication. Application can be viewed as an “elimination
--rule,” showing how to “eliminate” or use an implication in a proof.

-- ** Conjunction The expression and.intro h1 h2 builds a proof of p ∧ q using
-- proofs h1 : p and h2 : q. It is common to describe and.intro as the
-- and-introduction rule. In the next example we use and.intro to create a proof
-- of p → q → p ∧ q.

-- The example command states a theorem without naming it or storing it in the
-- permanent context. Essentially, it just checks that the given term has the
-- indicated type
example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq
