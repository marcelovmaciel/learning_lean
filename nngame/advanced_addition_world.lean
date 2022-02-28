-- * Level 1

theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b :=

begin

induction b,
apply succ_inj,
exact hs,
apply succ_inj,
exact hs,

end


-- * Level 2

theorem succ_succ_inj {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b :=

begin

apply succ_inj,
apply succ_inj,
exact h,

end
-- * Level 3

theorem succ_eq_succ_of_eq {a b : mynat} : a = b → succ(a) = succ(b) :=

begin

intro,
rw a_1,
refl,


end
-- * Level 4

theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b :=

begin

split,
exact succ_inj,
exact succ_eq_succ_of_eq,


end

-- * Level 5

theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=


begin

intro h,
induction t,
repeat{rw add_zero at h},
exact h,
repeat {rw add_succ at h},
rw succ_eq_succ_iff at h,
exact t_ih(h),

end
-- * Level 6

theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b :=

begin

intro h,
rw add_comm at h,
rw add_comm t b at h,
apply add_right_cancel,
exact h,


end

-- * Level 7
theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=


begin

intro h,
apply add_right_cancel,
exact h,

intro g,
rw g,
refl,


split,

end

-- * Level 8

lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 :=

begin

intro g,
rw <- add_zero (a) at g,
rw add_assoc at g,
rw zero_add b at g,
apply add_left_cancel,
exact g,

end

-- * Level 9
theorem succ_ne_zero (a : mynat) : succ a ≠ 0 :=
begin


symmetry,
exact zero_ne_succ a,

end
-- * Level 10

lemma add_left_eq_zero {{a b : mynat}} (H : a + b = 0) : b = 0 :=

begin

cases b,
rw add_zero at H,
refl,
rw add_succ at H,
exfalso,
apply succ_ne_zero,
exact H,

end

-- * Level 11
lemma add_right_eq_zero {a b : mynat} : a + b = 0 → a = 0 :=


begin

intro h,
rw add_comm at h,
exact add_left_eq_zero(h),

end
-- * Level 12

theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=

begin

symmetry,
rw succ_eq_add_one,
refl

end

-- * Level 13
lemma ne_succ_self (n : mynat) : n ≠ succ n :=

begin

symmetry at g,
have h := eq_zero_of_add_right_eq_self(g),
rw one_eq_succ_zero at h,
have h2 := succ_ne_zero(0),
intro g,
rw succ_eq_succ_iff at g,
rw <- add_one_eq_succ at g,
cases n,
apply zero_ne_succ 0,
exact h2(h)
end
