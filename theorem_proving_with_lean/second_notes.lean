-- -- * On propositions ----------------------------------------------------------
-- * Int [#64]
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


-- ** What differs theorem from def? [#85]
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

-- * Having fun with connectives [#15]
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


-- ** Conjunction [#10]

-- The expression and.intro h1 h2 builds a proof of p ∧ q using
-- proofs h1 : p and h2 : q. It is common to describe and.intro as the
-- and-introduction rule. In the next example we use and.intro to create a proof
-- of p → q → p ∧ q.





-- *** example command [#12]


-- The example command states a theorem without naming it or storing it in the
-- permanent context. Essentially, it just checks that the given term has the
-- indicated type
example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq




-- *** and.intro command [#33]


-- The expression and.intro h1 h2 builds a proof of p ∧ q using proofs h1 : p
-- and h2 : q. It is common to describe and.intro as the and-introduction rule.
-- In the next example we use and.intro to create a proof of p → q → p ∧ q. try
-- it!

example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq

--- *** and.elim_left, and.elim_right, and abbreviations: and.left, and.right

-- The expression and.elim_left h creates a proof of p from a proof h : p ∧ q.
-- Similarly, and.elim_right h is a proof of q. They are commonly known as the
-- right and left and-elimination rules. Because they are so commonly used, the
-- standard library provides the abbreviations and.left and and.right for
-- and.elim_left and and.elim_right, respectively.




-- COOL FACT

-- Notice that and-introduction and and-elimination are similar to the pairing
-- and projection operations for the cartesian product. The difference is that
-- given hp : p and hq : q, and.intro hp hq has type p ∧ q : Prop, while pair hp
-- hq has type p × q : Type. The similarity between ∧ and × is another instance
-- of the Curry-Howard isomorphism, but in contrast to implication and the
-- function space constructor, ∧ and × are treated separately in Lean. With the
-- analogy, however, the proof we have just constructed is similar to a function
-- that swaps the elements of a pair.

-- *** EXPLAINING THE WEIRD ⟨ ⟩ notation [#34]

-- We will see in Chapter 9 that certain types in Lean are structures, which is
-- to say, the type is defined with a single canonical constructor which builds
-- an element of the type from a sequence of suitable arguments. For every p q :
-- Prop, p ∧ q is an example: the canonical way to construct an element is to
-- apply and.intro to suitable arguments hp : p and hq : q. Lean allows us to
-- use anonymous constructor notation ⟨arg1, arg2, ...⟩ in situations like
-- these, when the relevant type is an inductive type and can be inferred from
-- the context. In particular, we can often write ⟨hp, hq⟩ instead of and.intro
-- hp hq:
variables  (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)

--- *** another syntatic sugar: h.left = and.left h
-- Lean provides another useful syntactic gadget. Given an expression e of an
-- inductive type foo (possibly applied to some arguments), the notation e.bar
-- is shorthand for foo.bar e. This provides a convenient way of accessing
-- functions without opening a namespace. For example, the following two
-- expressions mean the same thing:

variable l : list ℕ

#check list.head l
#check l.head

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

--- *** flattening right-associative constructors
example (h : p ∧ q) : q ∧ p ∧ q:= ⟨h.right, ⟨h.left, h.right⟩⟩
-- is equiv to
example (h : p ∧ q) : q ∧ p ∧ q:= ⟨h.right, h.left, h.right⟩


-- ** Disjunction [#1]

-- * or-introduction rules

-- The expression or.intro_left q hp creates a proof of p ∨ q from a proof hp :
-- p. Similarly, or.intro_right p hq creates a proof for p ∨ q using a proof hq
-- : q. These are the left and right or-introduction rules.
example (hp : p) : p ∨ q := or.intro_left q hp
example (hq : q) : p ∨ q := or.intro_right p hq

-- *** or-elimination rules [#15]

-- The or-elimination rule is slightly more complicated. The idea is that we can
-- prove r from p ∨ q, by showing that r follows from p and that r follows from
-- q. In other words, it is a proof by cases. In the expression or.elim hpq hpr
-- hqr, or.elim takes three arguments, hpq : p ∨ q, hpr : p → r and hqr : q → r,
-- and produces a proof of r. In the following example, we use or.elim to prove
-- p ∨ q → q ∨ p.
example (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)


-- *** abbreviation of or.intro left q hp = or.inl q (gotta assume hp !) [#15]

-- In most cases, the first argument of or.intro_right and or.intro_left can be
-- inferred automatically by Lean. Lean therefore provides or.inr and or.inl as
-- shorthand for or.intro_right _ and or.intro_left _. Thus the proof term above
-- could be written more concisely
-- This one sucks to read
example (h : p ∨ q) : q ∨ p := or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)


-- Because or has two constructors, we cannot use anonymous constructor
-- notation. But we can still write h.elim instead of or.elim h:
example (h : p ∨ q) : q ∨ p :=
h.elim
  (assume hp : p, or.inr hp)
  (assume hq : q, or.inl hq)
-- * Falsity [#6]

-- The connective false has a single elimination rule, false.elim, which
-- expresses the fact that anything follows from a contradiction. This rule is
-- sometimes called ex falso (short for ex falso sequitur quodlibet), or the
-- principle of explosion.

-- ** elimination rule: false.elim [#15]



-- They explain wwtf is ex falso

-- REVIEW THAT !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!


-- The connective false has a single elimination rule, false.elim, which
-- expresses the fact that anything follows from a contradiction. This rule is
-- sometimes called ex falso (short for ex falso sequitur quodlibet), or the
-- principle of explosion.

example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)

-- ** absurd [#10]
-- The arbitrary fact, q, that follows from falsity is an implicit argument in
-- false.elim and is inferred automatically. This pattern, deriving an arbitrary
-- fact from contradictory hypotheses, is quite common, and is represented by
-- absurd.

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

example (hnp : ¬p) (hq : q) (hqp : q → p) : r := absurd (hqp hq) hnp


-- ** introduction rule: true.intro [#6]

-- Incidentally, just as false has only an elimination rule, true has only an
-- introduction rule, true.intro : true, sometimes abbreviated trivial : true.
-- In other words, true is simply true, and has a canonical proof, trivial.


-- * Logical equivalence [#1]

-- ** iff.intro h₁ h₂, iff.elim_left, iff.elim_right [#15]

-- The expression iff.intro h1 h2 produces a proof of p ↔ q from h1 : p → q and
-- h2 : q → p. The expression iff.elim_left h produces a proof of p → q from h :
-- p ↔ q. Similarly, iff.elim_right h produces a proof of q → p from h : p ↔ q.
-- Here is a proof of p ∧ q ↔ q ∧ p:The expression iff.intro h1 h2 produces a
-- proof of p ↔ q from h1 : p → q and h2 : q → p. The expression iff.elim_left h
-- produces a proof of p → q from h : p ↔ q. Similarly, iff.elim_right h
-- produces a proof of q → p from h : p ↔ q. Here is a proof of p ∧ q ↔ q ∧ p:
theorem and_swap : p ∧ q ↔ q ∧ p :=
  iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from and.intro (and.right h) (and.left h))
  (assume h : q ∧ p,
    show p ∧ q, from and.intro (and.right h) (and.left h))

-- ** abreviating iff.elim_ : iff.mp and iff.mpr [#22]
#check and_swap p q

-- p ∧ q ↔ q ∧ p Because they represent a form of modus
-- ponens, iff.elim_left and iff.elim_right can be abbreviated iff.mp and
-- iff.mpr, respectively. In the next example, we use that theorem to derive q ∧
-- p from p ∧ q:
variable h2 : p ∧ q

example : q ∧ p := iff.mp (and_swap p q) h2

-- THIS NOTATION IS HARD AFF

-- We can use the anonymous constructor notation to construct a proof of p ↔ q
-- from proofs of the forward and backward directions, and we can also use .
-- notation with mp and mpr. The previous examples can therefore be written
-- concisely as follows:

theorem and_swap_again : p ∧ q ↔ q ∧ p :=
⟨ λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap_again p q).mp h

-- DIGEST THAT ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑

-- * Auxiliary Subgoals: have and suffices [#9]

-- NOW THIS IS FUN
example (h : p ∧ q) : q ∧ p :=

have hp : p, from and.left h, --- DIGEST THIS !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
have hq : q, from and.right h, --- DIGEST THIS !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
show q ∧ p, from and.intro hq hp


-- * Classical Logic: the em constructor [#62]
-- We basically need the excluded middle for lots of normal math. Constructively,
-- it is not in our toolset. For that we open the classical logic namespace


-- I USE THIS SHIT A LOT. WTF VELLEMAN


-- The introduction and elimination rules we have seen so far are all
-- constructive, which is to say, they reflect a computational understanding of
-- the logical connectives based on the propositions-as-types correspondence.
-- Ordinary classical logic adds to this the law of the excluded middle, p ∨ ¬p.
-- To use this principle, you have to open the classical namespace.


open classical

#check em p

-- One consequence of the law of the excluded middle is the principle of
-- double-negation elimination:

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

-- Double-negation elimination allows one to prove any proposition, p, by
-- assuming ¬p and deriving false, because that amounts to proving ¬¬p. In other
-- words, double-negation elimination allows one to carry out a proof by
-- contradiction, something which is not generally possible in constructive
-- logic.


-- TRICKy AS FUCK ⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡⇡

-- The classical axioms also give you access to additional patterns of proof
-- that can be justified by appeal to em. For example, one can carry out a proof
-- by cases or by contradiction.

example (h : ¬¬p) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, absurd h1 h)

example (h : ¬¬p) : p :=
by_contradiction
  (assume h1 : ¬p,
    show false, from h h1)


example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
or.elim (em p)
  (assume hp : p,
    or.inr
      (show ¬q, from
        assume hq : q,
        h ⟨hp, hq⟩))
  (assume hp : ¬p,
    or.inl hp)



-- * EXERCISES
-- in the supplemental file
