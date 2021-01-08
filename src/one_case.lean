import measure_theory.interval_integral
import analysis.special_functions.pow

open_locale real

example : 4 * ∫ (x : ℝ) in (0:ℝ)..1, real.sqrt(1 - x^2) = π :=
begin
  have : deriv (λ x : ℝ, 1/2 * (real.arcsin x + x * real.sqrt(1 - x^2) ) ) = λ x, real.sqrt(1 - x^2),
  { ext,
    rw deriv_const_mul,
    rw deriv_add,
    simp only [one_div, real.deriv_arcsin],
    rw deriv_mul,
    simp only [one_mul, deriv_id''],
    rw deriv_sqrt,
    simp only [differentiable_at_const, mul_one, zero_sub, deriv_sub, differentiable_at_id', deriv_pow'', nat.cast_bit0, deriv_id'',
  deriv_const', pow_one, differentiable_at.pow, nat.cast_one],
    rw neg_div,
    rw mul_div_mul_left _ _ (show (2 : ℝ) ≠ 0, by norm_num),
    field_simp,
    rw add_left_comm,
    rw div_add_div_same,
    sorry
  },
  sorry
end