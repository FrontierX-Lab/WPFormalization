import Mathlib

/-! Exact stable Gamma splitting in binomial form. -/
noncomputable section
namespace WP
lemma gamma_split_binomial (N k : ℕ) (hk : k ≤ N) :
    Real.Gamma ((k : ℝ)+1)*Real.Gamma ((N-k : ℕ)+1)/Real.Gamma ((N+2 : ℕ)+1) =
      1/(((N : ℝ)+2)*((N : ℝ)+1)*(N.choose k : ℝ)) := by
  rw [Real.Gamma_nat_eq_factorial,Real.Gamma_nat_eq_factorial,Real.Gamma_nat_eq_factorial]
  have hch : (0 : ℝ) < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have he := Nat.choose_mul_factorial_mul_factorial hk
  have heR : (N.choose k : ℝ)*(k.factorial : ℝ)*(N-k).factorial = N.factorial := by exact_mod_cast he
  have hfac : ((N+2).factorial : ℝ) = ((N : ℝ)+2)*((N : ℝ)+1)*(N.factorial : ℝ) := by
    rw [show N+2=(N+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  field_simp [hch.ne',show (0 : ℝ) < (N.factorial : ℝ) by positivity]
  nlinarith [heR]
lemma gamma_split_binomial_complexity (h h₁ h₂ : ℕ)
    (h₁p : 1 ≤ h₁) (h₂p : 1 ≤ h₂) (hs : h₁+h₂+1=h) :
    Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h =
      1/(((h : ℝ)-1)*((h : ℝ)-2)*((h-3).choose (h₁-1) : ℝ)) := by
  have hN : h₁-1 ≤ h-3 := by omega
  have h₁' : (h₁ : ℝ) = ((h₁-1 : ℕ) : ℝ)+1 := by
    rw [Nat.cast_sub h₁p]
    push_cast
    ring
  have h₂' : (h₂ : ℝ) = (((h-3)-(h₁-1) : ℕ) : ℝ)+1 := by
    rw [show (h-3)-(h₁-1)=h₂-1 by omega,Nat.cast_sub h₂p]
    push_cast
    ring
  have h' : (h : ℝ) = (((h-3)+2 : ℕ) : ℝ)+1 := by
    have he : (h-3)+2+1=h := by omega
    exact_mod_cast he.symm
  rw [h₁',h₂',h',gamma_split_binomial (h-3) (h₁-1) hN]
  simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_sub (show 3 ≤ h by omega)]
  ring
end WP
