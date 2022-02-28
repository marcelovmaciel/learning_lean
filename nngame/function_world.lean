
-- Level 1
example (P Q : Type) (p : P) (h : P → Q) : Q :=

begin

exact h p

end
-- * Level 2

import mynat.add -- + on mynat
import mynat.mul -- * on mynat


example : mynat → mynat :=

begin

intro n,
exact 3*n+2

end

-- *  Level 3

example (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=

begin

have q : Q := h(p),
have t : T := j(q),
have u : U := l(t),
exact u

end
-- Level 4
example (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=

begin
have q : Q := h(p),
have t : T := j(q),
have u : U := l(t),
exact u

end

-- Level 5

example (P Q : Type) : P → (Q → P) :=

begin

intro p,
intro q,
exact p

end

-- Level 6
example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=

begin

intro f,
intro g,
intro h,

have j := f h,

apply j,
apply g,
exact h

end
-- Level 7
example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=

begin
intros f h p,
exact h(f(p))
end
-- Level 8

example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) :=

begin

intros f h p,
apply h,
apply f,
exact p

end
