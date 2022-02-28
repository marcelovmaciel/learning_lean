-- * Introducing lean ---------------------------------------------------------
-- in which I read https://leanprover.github.io/theorem_proving_in_lean
-- * Quick typing
/- declare some constants -/

-- constant m : nat        -- m is a natural number
-- constant n : nat
-- constants b1 b2 : bool  -- declare two constants at once

/- check their types -/

#check m            -- output: nat
#check n
#check n + 0        -- nat
#check m * (n + 0)  -- nat
#check b1           -- bool
#check b1 && b2     -- "&&" is boolean and
#check b1 || b2     -- boolean or
#check tt           -- boolean "true"

-- Try some examples of your own.


constant f : nat → nat           -- type the arrow as "\to" or "\r"
constant f' : nat -> nat         -- alternative ASCII notation
constant f'' : ℕ → ℕ             -- alternative notation for nat
constant p : nat × nat           -- type the product as "\times"
constant q : prod nat nat        -- alternative notation
constant g : nat → nat → nat
constant g' : nat → (nat → nat)  -- has the same type as g!
constant h : nat × nat → nat

constant F : (nat → nat) → nat   -- a "functional"

#check f               -- ℕ → ℕ
#check f n             -- ℕ
#check g m n           -- ℕ
#check g m             -- ℕ → ℕ
#check (m, n)          -- ℕ × ℕ
#check p.1             -- ℕ
#check p.2             -- ℕ
#check (m, n).1        -- ℕ
#check (p.1, n)        -- ℕ × ℕ
#check F f             -- ℕ




-- * Lambda abstraction
-- How does one define a function in lean?
-- Using the fun or lambda abstraction
#check fun x : nat, x + 5
#check λ x : nat, x + 5

constants α β  : Type
constants a1 a2 : α
constants b1 b2 : β

constant f2 : α → α
constant g2 : α → β
constant h2 : α → β → α
constant p2 : α → α → bool

#check fun x : α, f2 x                      -- α → α
#check λ x : α, f2 x                        -- α → α
#check λ x : α, f2 (f2 x)                    -- α → α
#check λ x : α, h2 x b1                     -- α → α
#check λ y : β, h2 a1 y                     -- β → α
#check λ x : α, p2 (f2 (f2 x)) (h2 (f2 a1) b2)  -- α → bool
#check λ x : α, λ y : β, h2 (f2 x) y         -- α → β → α
#check λ (x : α) (y : β), h2 (f2 x) y        -- α → β → α
#check λ x y, h2 (f2 x) y                    -- α → β → α

constants γ : Type

#check λ b : β, λ x : α, x     -- β → α → α
#check λ (b : β) (x : α), x    -- β → α → α
#check λ (g : β → γ) (f : α → β) (x : α), g (f x)
                              -- (β → γ) → (α → β) → α → γ


constants m n : nat
constant b : bool

#print "reducing pairs"
#check (m, n).1
#reduce (m, n).1        -- m
#reduce (m, n).2        -- n

#print "reducing boolean expressions"
#reduce tt && ff        -- ff
#reduce ff && b         -- ff
#reduce b && ff         -- bool.rec ff ff b

#print "reducing arithmetic expressions"
#reduce n + 0           -- n
#reduce n + 2           -- nat.succ (nat.succ n)
#reduce 2 + 3           -- 5

example:  2 + 3 == 5 :=

begin
refl,
end

-- definitional equality ensues when #reduce leads to the same thing !
-- we can also eval stuff in lean

#eval 12345 * 54321 -- fancy hehehehe

-- * Defining things

-- This is huge. Defining things hehehehehehe




def foo : (ℕ → ℕ) → ℕ := λ f, f 0

#check foo    -- (ℕ → ℕ) → ℕ
#print foo    -- λ (f : ℕ → ℕ), f 0
--
--
def double (x : ℕ) : ℕ := x + x
#print double
#check double 3
#reduce double 3    -- 6

def square (x : ℕ) := x * x
#print square
#check square 3
#reduce square 3    -- 9

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)
#check do_twice
#check do_twice double

#reduce do_twice double 2    -- 8

-- These definitions are equivalent to the following:
def double' : ℕ → ℕ := λ x, x + x
def square' : ℕ → ℕ := λ x, x * x
def do_twice' : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

-- As an exercise, we encourage you to use do_twice and double to define
-- functions that quadruple their input, and multiply the input by 8.

def quadruple (x : ℕ) := do_twice double x
def eightuple (x : ℕ) := double (quadruple x)


#reduce quadruple 3
#reduce eightuple 3
#eval eightuple 3

-- As a further exercise, we encourage you to try defining a function Do_Twice :
-- ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) which applies its argument twice, so
-- that Do_Twice do_twice is a function that applies its input four times. Then
-- evaluate Do_Twice do_twice double 2.
def Do_twice (f: (ℕ → ℕ) → (ℕ → ℕ)) (g: ℕ → ℕ) (x : ℕ) := f g x

#check Do_twice
#reduce Do_twice do_twice double 2


def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := λ a b, f(a,b)
#check curry


def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := λ ab, (f ab.1 ab.2)
#check uncurry

-- ** Local assignments
-- Local assignments are done with let
#check let y := 2 + 2 in y * y   -- ℕ
#reduce  let y := 2 + 2 in y * y   -- 16

def t (x : ℕ) : ℕ :=
let y := x + x in y * y

-- You can also do nested assignments in in a let
#reduce  let y := 2 + 2, z := y + y in z * z



-- * Code organization

-- jump this and read what is discussed after loc 211
section useful
variables (α β γ : Type*)
variables (g : β → γ) (f : α → β) (h : α → α)
variable x : α

def compose3 := g (f x)
def do_twice3 := h (h x)
def do_thrice3 := h (h (h x))
end useful


-- variables is a way of creating bound variables to be inserted in definitions
-- that use them. So we don't keep declaring the same thing over and over again
-- but it is safer than declare those as global constants
variables (α β γ : Type*)
variables (g : β → γ) (f : α → β) (h : α → α)
variable x : α

def compose := g (f x)
def do_twice2 := h (h x)
def do_thrice := h (h (h x))

#print compose
#print do_twice2
#print do_thrice


-- When declared in this way, a variable stays in scope until the end of the
-- file we are working on, and we cannot declare another variable with the same
-- name.

-- If we don't want that, we can create LOCAL SCOPES for variables
-- using the ~section~ command
-- Note that if we try to put it HERE it will give an error
-- if we put it BEFORE the global definition it works, though


-- ** Namespace
-- Another organizational tools are namespaces
-- Kinda like modules (from julia)
-- while sections are kinda like local_scopes for variables

namespace foo

def a : ℕ := 5
-- note that if I call it f it would conflict with my previously named f in the
-- global scope.
def f2 (x : ℕ) : ℕ := x + 7

def fa : ℕ := f2 a
def ffa : ℕ := f2 (f2 a)



#print "inside foo"

#check a
#check f2
#check fa
#check ffa
#check foo.fa
end foo

open foo

#print "opened foo"

#check a
#check f
#check fa
#check foo.fa

-- *** On the difference between sections and namespaces
-- Namespaces and sections serve different purposes: namespaces organize data
-- and sections declare variables for insertion in theorems. In many respects,
-- however, a namespace ... end block behaves the same as a section ... end
-- block. In particular, if you use the variable command within a namespace, its
-- scope is limited to the namespace. Similarly, if you use an open command
-- within a namespace, its effects disappear when the namespace is closed.


-- * Dependent types

-- This is freaking hard. I gotta digest that better

-- This is an instance of a Pi type, or dependent function type. Given α : Type
-- and β : α → Type, think of β as a family of types over α, that is, a type β a
-- for each a : α. In that case, the type Π x : α, β x denotes the type of
-- functions f with the property that, for each a : α, f a is an element of β a.
-- In other words, the type of the value returned by f depends on its input.
-- Notice that Π x : α, β makes sense for any expression β : Type. When the
-- value of β depends on x (as does, for example, the expression β x in the
-- previous paragraph), Π x : α, β denotes a dependent function type. When β
-- doesn’t depend on x, Π x : α, β is no different from the type α → β. Indeed,
-- in dependent type theory (and in Lean), the Pi construction is fundamental,
-- and α → β is just notation for Π x : α, β when β does not depend on x.

-- For more on that see cite:mimram2020proof


-- In the coming chapters, you will come across many instances of dependent
-- types. Here we will mention just one more important and illustrative example,
-- the Sigma types, Σ x : α, β x, sometimes also known as dependent products.
-- These are, in a sense, companions to the Pi types. The type Σ x : α, β x
-- denotes the type of pairs sigma.mk a b where a : α and b : β a.

-- Just as Pi types Π x : α, β x generalize the notion of a function type α → β
-- by allowing β to depend on α, Sigma types Σ x : α, β x generalize the
-- cartesian product α × β in the same way: in the expression sigma.mk a b, the
-- type of the second element of the pair, b : β a, depends on the first element
-- of the pair, a : α.


-- Basically, we have two fundamental dependent type constructors:
-- Π and Σ
-- * implicit arguments


-- are those that are tedious to keep declaring, but that lean can infer from
-- context. So we tell Lean to leave those as implicit

namespace hidden
universe u
constant list : Type u → Type u

namespace list

constant cons   : Π α_2 : Type u, α_2 → list α_2 → list α_2
constant nil    : Π α_2 : Type u, list α_2
constant append : Π α_2 : Type u, list α_2 → list α_2 → list α_2

end list

end hidden

open hidden.list

variable  α_2 : Type
variable  a : α_2
variables l1 l2 : hidden.list α_2

#check cons α_2 a (nil α_2)
#check append α_2 (cons α_2 a (nil α_2)) l1
#check append α_2 (append α_2 (cons α_2 a (nil α_2)) l1) l2

-- note how ↑↑↑ I keep declaring everything all the time;
-- not how ↓↓↓↓ I keep it as underscores, but still not good enough;

#check cons _ a (nil _)
#check append _ (cons _ a (nil _)) l1
#check append _ (append _ (cons _ a (nil _)) l1) l2


-- It is still tedious, however, to type all these underscores. When a function
-- takes an argument that can generally be inferred from context, Lean allows us to
-- specify that this argument should, by default, be left implicit. This is done by
-- putting the arguments in __curly braces__, as follows:
namespace list2
constant cons   : Π {α : Type u}, α → list α → list α
constant nil    : Π {α : Type u}, list α
constant append : Π {α : Type u}, list α → list α → list α
end list2

open list2

variable  α_3 : Type
variable  a_2 : α_3
variables l11 l12 : list α_3

#check cons a_2 list2.nil
#check list2.append (cons a_2 nil) l11
#check list2.append (list2.append (list2.cons a_2 list2.nil) l11) l12
-- note how I let go of the bothersome type declaration everywhere


-- also useful in functions
universe u
def ident {α : Type u} (x : α) := x

variables α_4 β_4 : Type u
variables (a_3 : α_4) (b : β_4)

#check ident      -- ?M_1 → ?M_1
#check ident a_3    -- α
#check ident b    -- β



-- Lean assumes that numerals are natural numbers!! Numerals are overloaded in
-- Lean, but when the type of a numeral cannot be inferred, Lean assumes, by
-- default, that it is a natural number.
-- Sometimes, however, we may find ourselves in a situation where we have declared an argument to a function to be implicit, but now want to provide the argument explicitly. If foo is such a function, the notation @foo denotes the same function with all the arguments made explicit.
-- try it!

variable again : α
variables bzinho : β

#check @id        -- Π {α : Type u_1}, α → α
#check @id α      -- α → α
#check @id β      -- β → β
#check @id α again    -- α
#check @id β bzinho    -- β
-- *
