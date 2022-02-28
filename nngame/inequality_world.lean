-- * Level 1
import mynat.le

lemma one_add_le_self (x : mynat) : x ≤ 1 + x :=


begin

use 1,
rw add_comm,

end

-- * Level 2
lemma le_refl (x : mynat) : x ≤ x :=

begin


use 0,
refl

end
-- * Level 3

theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) :=

begin

intro h,
rw le_iff_exists_add at h ⊢,
cases h with c hc,
use c+1,
rw succ_eq_add_one,
rw hc,
refl,

end

-- * Level 4

lemma zero_le (a : mynat) : 0 ≤ a :=

begin

rw le_iff_exists_add,
use a,
rw zero_add,
refl,


end

-- * Level 5
theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin

rw le_iff_exists_add at hab hbc,
cases hbc,
cases hab,
rw hab_h at hbc_h,
use hab_w + hbc_w,
rw add_assoc at hbc_h,
apply hbc_h,
end


-- * Level 6
theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b :=

begin

cases hab,
cases hba,
rw hab_h at hba_h,
rw add_assoc at hba_h,
symmetry at hba_h,
have h := eq_zero_of_add_right_eq_self hba_h,
have g := add_right_eq_zero(h),
rw g at hab_h,
rw add_zero at hab_h,
symmetry at hab_h,
exact hab_h,


end

-- * Level 7
lemma le_zero (a : mynat) (h : a ≤ 0) : a = 0 :=


begin

cases h,
symmetry at h_h,
exact add_right_eq_zero(h_h),

end
-- * Level 8
lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b :=
begin
rw le_iff_exists_add at h,
cases h,
repeat {rw succ_eq_add_one},
rw h_h,
rw add_right_comm,
rw le_iff_exists_add,
use h_w,
refl,
end
-- * Level 9
-- couldnt do it
theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
begin
sorry
end

-- * Level 10
lemma le_succ_self (a : mynat) : a ≤ succ a :=


begin
apply le_succ,
exact le_refl a,
end

-- * Level 11

theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=


begin
intro h,
intro t,
rw le_iff_exists_add ,
rw le_iff_exists_add at h,
cases h,
use h_w,
rw h_h,
rw add_right_comm,
refl,
end

-- * Level 12
theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b :=
begin
intro h,
rw le_iff_exists_add at h,
cases h,
rw le_iff_exists_add,
use h_w,
rw succ_add at h_h,
have foo:= succ_inj(h_h),
exact foo,
end

-- * Level 13
theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=


begin

intro h,
rw le_iff_exists_add at h,
cases h,
induction a,
rw succ_add at h_h,
rw zero_add at h_h,
symmetry at h_h,
have foo :=  succ_ne_zero h_w,
exact foo h_h,
rw succ_add at h_h,
have foo2 := succ_inj(h_h),
exact a_ih(foo2),


end

-- * Level 14

theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=


begin

cases h,
use h_w,
rw h_h,
rw add_assoc,
refl,

end

-- * Level 15
lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=


begin

intro h,
cases h with r l,
cases r with f1 f2,
cases f1,
rw add_zero at f2,
exfalso,
apply l,
rw f2,

apply le_refl a,
rw le_iff_exists_add,
rw add_succ at  f2,
use f1,
rw succ_add,
apply f2,

end

-- * Level 16
lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=


begin

intro h,
split,
rw le_iff_exists_add at h,
rw le_iff_exists_add,
cases h,
rw ← add_one_eq_succ at h_h,
rw add_assoc at h_h,
use (1 + h_w),
exact h_h,
by_contra h2,
have foo3 := le_trans (succ a) b a h h2,
have foo4 := not_succ_le_self a,
exact foo4(foo3),
No Results
end
-- * Level 17

lemma lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b :=
begin

split,
exact lt_aux_one a b,
exact lt_aux_two a b,


end
