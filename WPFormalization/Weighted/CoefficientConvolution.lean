import WPFormalization.Analysis.HarmonicMass
import WPFormalization.Analysis.ThetaNonnegative
import WPFormalization.Statements.Comparison
/-! Exact harmonic coefficient convolution and nonnegativity of the genuine
finite linear weights, on the full closed parameter interval. -/
noncomputable section
namespace WP
lemma harmonicCoeff_convolution (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (h₁ h₂ m : ℕ) :
    (∑ k ∈ Finset.range (m+1), harmonicCoeff Y h₁ k*harmonicCoeff Y h₂ (m-k)) =
      harmonicCoeff Y (h₁+h₂) m := by
  simp_rw [Analysis.harmonicCoeff_eq_formal Y hY]
  rw [pow_add,PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
lemma linearQ_nonneg (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (h m l : ℕ) (hh : 2 ≤ h) :
    0 ≤ linearQ Y h m l := by
  unfold linearQ
  exact div_nonneg (mul_nonneg (theta_nonneg Y hY l)
    (harmonicCoeff_pos Y (h-1) (m-l) (by omega) hY).le)
    (harmonicCoeff_pos Y h m (by omega) hY).le
lemma theta_zero_closed (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) : theta Y 0 = 1 := by
  simp [theta,realCoeff,coeff,Analysis.barK_zero_closed Y hY]
lemma linearQ_zero_pos (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (h m : ℕ) (hh : 2 ≤ h) :
    0 < linearQ Y h m 0 := by
  unfold linearQ
  rw [theta_zero_closed Y hY]
  simp only [Nat.sub_zero,one_mul]
  exact div_pos (harmonicCoeff_pos Y (h-1) m (by omega) hY)
    (harmonicCoeff_pos Y h m (by omega) hY)
lemma linearS₀_nonneg (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (h m : ℕ) (hh : 2 ≤ h) :
    0 ≤ linearS₀ Y h m := by
  apply Finset.sum_nonneg
  intro l hl
  exact linearQ_nonneg Y hY h m l hh
lemma linearQ_zero_le_sum (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (h m : ℕ) (hh : 2 ≤ h) :
    linearQ Y h m 0 ≤ linearS₀ Y h m := by
  apply Finset.single_le_sum
  · intro l hl; exact linearQ_nonneg Y hY h m l hh
  · simp
lemma linearS₀_tail (Y : ℝ) (h m : ℕ) :
    linearS₀ Y h m-linearQ Y h m 0 = ∑ l ∈ Finset.range m, linearQ Y h m (l+1) := by
  unfold linearS₀
  rw [Finset.sum_range_succ']
  ring
end WP
