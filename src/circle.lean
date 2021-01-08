import data.real.basic analysis.special_functions.trigonometric
import measure_theory.interval_integral
import analysis.special_functions.pow

open_locale real
noncomputable theory
open interval_integral

example : ∫ (x : ℝ) in 0..1, x = 1/2 :=
begin
  have : deriv (λ x : ℝ, x^2/2) = λ x, x,
  { ext x,
    simp, field_simp, ring },
  simp only [← this],
  rw integral_deriv_eq_sub,
  { norm_num },
  { simp },
  { rw this,
    exact continuous_id.continuous_on }
end

example (r : ℝ) : deriv (λ x : ℝ, (real.sqrt (r^2 - x^2))) = λ x, (-x/real.sqrt (r^2 - x^2)) :=
begin
  ext,
  rw deriv_sqrt,
  {
    simp only [differentiable_at_const, mul_one, zero_sub, deriv_sub, differentiable_at_id', deriv_pow'', nat.cast_bit0, deriv_id'',
  deriv_const', pow_one, differentiable_at.pow, nat.cast_one, mul_zero], 
    sorry
  },
  { 
    sorry
  },
  {
    
  }
end

example (r : ℝ) (x : ℝ) : 4 * ∫ x in (0: ℝ)..r, (real.sqrt (r^2 - x^2)) = π*r^2 :=
begin
  have : deriv (λ x : ℝ, (real.sqrt (r^2 - x^2))) = λ x, (-x/real.sqrt (r^2 - x^2)),
  { ext, sorry

  },
  sorry
end



