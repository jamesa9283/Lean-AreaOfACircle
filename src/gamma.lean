import analysis.special_functions.exp_log analysis.special_functions.pow


open_locale big_operators nat
noncomputable theory
open complex

def poch (a : ℂ) (n : ℕ) := ∏ i in finset.range n, a + n

def rΓ_series (z : ℂ) (n : ℕ) := poch z (n + 1) / (n! * exp (z * log n)) 

def Γ_series (z : ℂ) (n : ℕ) := (n! : ℂ) * exp(z * log n) / poch z (n + 1)
def Γ_series' (z : ℂ) (n : ℕ) := ((n - 1)! : ℂ) * exp (z * log n) / poch z n

lemma rΓ_eq_inv_Γ (z : ℂ) (n : ℕ) : Γ_series z n = (rΓ_series z n)⁻¹ := by field_simp [rΓ_series, Γ_series]

def ln_Gamma_series (z : ℂ) (n : ℕ) := z * log (n) - log z - ∑ k in finset.range n, log(z / (k+1) + 1)

lemma lnG_def (z : ℂ) (n : ℕ) : ln_Gamma_series z n = z * log (n) - log z - ∑ k in finset.range n, log(z / (k+1) + 1) := rfl

def ln_Gamma (x : ℝ) := x

-- let us asssume convergence, because I don't know how to prove it.
lemma ln_Γ_complex_converges (z : ℂ) (n : ℕ) : filter.tendsto (ln_Gamma_series z) (filter.at_top) (nhds z) :=
begin
  
  sorry
end
