import WPFormalization.Statements.Basic

/-! Positivity before the first real Bessel zero, proved directly from the infimum
definition, continuity and the actual real-axis derivative jets. -/
noncomputable section
namespace WP
lemma a_ne_zero (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : a Y ≠ 0 := by
  intro ha
  by_cases hzero : Y = 0
  · simpa [hzero, a_zero] using ha
  have hroot : deriv X (Y : ℂ) = 0 := by
    apply Complex.ext
    · simpa only [a, Complex.zero_re] using ha
    · simpa only [iteratedDeriv_one, Complex.zero_im] using iteratedDeriv_X_im_ofReal 1 Y
  have hYpos : 0 < Y := lt_of_le_of_ne hY.1 (Ne.symm hzero)
  have hle : y₀ ≤ Y := csInf_le (by
    refine ⟨0, ?_⟩
    intro x hx
    exact hx.1.le) ⟨hYpos, hroot⟩
  linarith [hY.2]
lemma a_pos (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 < a Y := by
  have hcont : Continuous a := by
    unfold a
    have hd : Continuous (deriv X) := by
      simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
    exact Complex.continuous_re.comp (hd.comp Complex.continuous_ofReal)
  by_contra h
  have hle : a Y ≤ 0 := not_lt.mp h
  obtain ⟨t,ht,hat⟩ := intermediate_value_Icc' hY.1 hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (a Y) (a 0) from ⟨hle, by rw [a_zero]; norm_num⟩)
  exact a_ne_zero t ⟨ht.1,lt_of_le_of_lt ht.2 hY.2⟩ hat

lemma derivX_ofReal (Y : ℝ) : deriv X (Y : ℂ) = (a Y : ℂ) := by
  apply Complex.ext
  · simp [a]
  · simpa only [iteratedDeriv_one, Complex.ofReal_im] using iteratedDeriv_X_im_ofReal 1 Y


end WP
