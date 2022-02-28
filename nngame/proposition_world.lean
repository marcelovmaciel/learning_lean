-- *  Level 1

example (P Q : Prop) (p : P) (h : P → Q) : Q :=


begin

exact h(p)

end

-- * Level 2

lemma imp_self (P : Prop) : P → P :=


begin
intro p,
exact p
end

-- * Level 3

lemma maze (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=


begin
exact l(j(h(p)))
end
-- * Level 4
lemma maze2 (P Q R S T U: Prop)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=

begin

exact l(j(h(p)))

end

-- * Level 5
example (P Q : Prop) : P → (Q → P) :=


begin


intro p,
intro q,
exact p

end
-- * Level 6
example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) :=

begin
intros f g p,
apply f p,
apply g,
exact p
end
-- * Level 7
lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) :=


begin

intros hpq hqr p,
exact hqr(hpq(p))

end
-- * Level 8
lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=


begin
repeat {rw not_iff_imp_false},
intros f h e,
exact h(f(e))

end

-- * Level 9
example (A B C D E F G H I J K L : Prop)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L :=

begin
cc
end
