import Mathlib.Analysis.SpecialFunctions.Stirling
/-! Effective inverse-Poisson-peak normalization from Mathlib Stirling monotonicity. -/
noncomputable section
namespace WP.Analysis

def poissonPeakInverse (k : ℕ) : ℝ :=
  (k.factorial:ℝ)*Real.exp (k:ℝ)/(k:ℝ)^k

lemma poissonPeakInverse_pos (k : ℕ) : 0 < poissonPeakInverse k := by
  unfold poissonPeakInverse
  cases k with
  | zero => norm_num [Real.exp_zero]
  | succ k => positivity

lemma poissonPeakInverse_eq_stirling (k : ℕ) (hk : 1 ≤ k) :
    poissonPeakInverse k=Stirling.stirlingSeq k*Real.sqrt (2*(k:ℝ)) := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast hk
  have hexp : Real.exp (k:ℝ)=(Real.exp 1)^k := by
    simpa only [mul_one] using Real.exp_nat_mul 1 k
  rw [poissonPeakInverse,Stirling.stirlingSeq,div_pow,hexp]
  field_simp

lemma poissonPeakInverse_le (k : ℕ) (hk : 1 ≤ k) :
    poissonPeakInverse k ≤ Real.exp 1*Real.sqrt (k:ℝ) := by
  have hs : Stirling.stirlingSeq k ≤ Real.exp 1/Real.sqrt 2 := by
    have ht := Stirling.stirlingSeq'_antitone (show 0 ≤ k-1 by omega)
    simpa only [Function.comp_apply,Nat.succ_eq_add_one,Nat.zero_add,
      Nat.sub_add_cancel hk,Stirling.stirlingSeq_one] using ht
  rw [poissonPeakInverse_eq_stirling k hk]
  calc _ ≤ (Real.exp 1/Real.sqrt 2)*Real.sqrt (2*(k:ℝ)) :=
          mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
       _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)];field_simp

end WP.Analysis
