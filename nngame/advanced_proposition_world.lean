-- * Level 1
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=


begin

split,
exact p,
exact q

end


-- * Level 2

lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P :=

begin

intro h,
cases h with p q,
split,
exact q,
exact p
end

-- * Level 3
lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R :=


begin

intros h q,
cases h,
cases q,
split,
exact h_left,
exact q_right

end
-- * Level 4
lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=


begin
intros h g,
cases h with hpq hqp,
cases g with gpr grp,
split,
intro p,
exact gpr(hpq(p)),
intro r,
exact hqp(grp(r))
end
-- * Level 5

lemma iff_trans2 (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=

begin
intros h g,
cases h with hpq hqp,
cases g with gpr grp,
split,
intro p,
exact gpr(hpq(p)),
intro r,
exact hqp(grp(r))

end
-- * Level 6
example (P Q : Prop) : Q → (P ∨ Q) :=

begin
intro g,
right,
exact g
end

-- * Level 7

lemma or_symm (P Q : Prop) : P ∨ Q → Q ∨ P :=

begin

intro h,
cases h with p q,
right,
exact p,
left,
exact q


end

-- * Level 8
lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=


begin
split,
intro h,
cases h with hp hqor,
cases hqor with q r,
left,
split,
exact hp,
exact q,
right,
split,
exact hp,
exact r,

intro g,
split,
cases g with pq pr,
cases pq with p q,
exact p,
cases pr with p r,
exact p,
cases g with pq pr,
left,
cases pq with p q,
exact q,
right,
cases pr with p r,
exact r

end
-- * Level 9
import tactic.tauto


lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=


begin

intro h,
exfalso,
cases h with p p2,
apply p2,
exact p


end

-- * Level 10
import tactic.tauto
local attribute [instance, priority 10] classical.prop_decidable -- we are mathematicians
lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) :=

begin

by_cases p : P; by_cases q : Q,
repeat {cc}


end
