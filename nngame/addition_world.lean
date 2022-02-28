--- Due to some path related stuff, it doesn't run, but I'll keep them here
-- * Level 1
import mynat.definition -- Imports the natural numbers.
import mynat.add -- imports addition.
--
lemma zero_add (n : mynat) : 0 + n = n :=

begin
induction n with d hd,
rw add_zero,
refl,
rw add_succ,
rw hd,
refl

end


-- * Level 2
lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=


begin

induction c with d hd,
rw add_zero (a + b),
refl,

rw add_succ (a + b) d,
rw add_succ b d,
rw hd,
refl
end
-- * Level 3
lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=

begin
induction b with d hd,
rw add_zero (succ a),
refl,
rw add_succ (succ a) (d),
rw hd,
refl
end

-- * Level 4
lemma add_comm (a b : mynat) : a + b = b + a :=

begin
rw zero_add,
refl,
rw add_succ a d,
rw hd,
rw <- succ_add,
refl
end

-- *  Level 5
theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=

begin

induction n with d hd,
rw one_eq_succ_zero,
rw zero_add (succ 0),
refl,
rw one_eq_succ_zero,

end
-- * Level 6
lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=


begin
rw add_assoc,
rw add_comm b c,
rw <- add_assoc,
refl
end
