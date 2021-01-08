import data.real.basic analysis.special_functions.trigonometric
import measure_theory.interval_integral
import data.real.sqrt

localized "notation `π` := real.pi" in real

open_locale filter
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

def f (x : ℝ) := real.sqrt x

example (r : ℝ) (x : ℝ) : ∫ x in (0: ℝ)..r, (real.sqrt (x^2 - r^2)) = PI*r^2 :=
begin

  sorry
end



