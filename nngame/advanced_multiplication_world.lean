-- *  Level 1
import game.world3.level9

theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=


begin

intro h,
intro g,
intro f,
cases b,
rw mul_zero at f,
apply g,
exact f,
apply h,
rw mul_succ at f,
have foo := add_left_eq_zero(f),
exact foo,

end

-- * Level 2

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :  a = 0 ∨ b = 0 :=

begin

cases b,
right,
rw mul_zero at h,
exact h,
left,
rw mul_succ at h,
have foo := add_left_eq_zero(h),
exact foo,

end
-- * Level 3
theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 :=


begin

split,
apply eq_zero_or_eq_zero_of_mul_eq_zero,
intro g,
cases g,
rw g,
rw zero_mul,
refl,
rw g,
rw mul_zero,
refl

end
-- * Level 4
-- Couldn't do it lol
