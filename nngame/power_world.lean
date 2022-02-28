import mynat.pow

-- *  Level 1
lemma zero_pow_zero : (0 : mynat) ^ (0 : mynat) = 1 :=

begin

rw pow_zero,
refl

end

-- * Level 2
lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 :=


begin

induction m,
rw pow_succ,
rw pow_zero,
rw mul_zero,
refl,
rw pow_succ,

end

-- * Level 3
lemma pow_one (a : mynat) : a ^ (1 : mynat) = a :=

begin

induction a,
rw one_eq_succ_zero,
rw pow_succ,
rw mul_zero,
refl,
rw one_eq_succ_zero,
rw pow_succ,

end

-- * Level 4

lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=


begin

induction m,
rw pow_zero,
refl,
rw pow_succ,
rw m_ih,
rw mul_one,
refl

end
-- * Level 5

lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n :=

begin

induction n,
rw pow_zero,
rw mul_one,
rw add_zero,
refl,
rw pow_succ,
rw add_comm,
rw succ_add,
rw pow_succ,
rw add_comm,

end

-- * Level 6
lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=


begin

repeat {rw pow_succ },
rw n_ih,
simp,

end
-- * Level 7

lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) :=

begin

induction n,
rw mul_zero,
repeat {rw pow_zero},
repeat {rw pow_succ},
rw mul_succ,
rw n_ih,
rw pow_add,
refl,

end

-- * Level 8
lemma add_squared (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b :=


begin
rw two_eq_succ_one,
rw one_eq_succ_zero,
repeat {rw pow_succ},
repeat {rw pow_zero},
repeat {rw one_mul},
simp,
rw mul_succ,
rw <- one_eq_succ_zero,
rw mul_one,
repeat {rw add_mul},
repeat {rw mul_add},
simp,
end
