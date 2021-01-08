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

def ln_Gamma (x : ℝ) := x

lemma ln_Γ_complex_converges (x : ℝ) (n : ℝ) : ∃ c : ℂ, filter.tends_to Γ_series c :=
