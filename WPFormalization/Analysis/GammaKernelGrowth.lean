import WPFormalization.Analysis.GammaLaplaceKernel

/-! The actual Gamma-ratio Laplace kernel is uniformly bounded on each positive ray tail. The estimate is proved from the explicit real quotient and the genuine removable complex germ, with no asymptotic input. -/
noncomputable section
namespace WP.Analysis
lemma gammaLogRatioKernel_tail_bound (a r : ℝ) (ha : 0<a) (hr : 0<r)
    (t : ℝ) (hrt : r≤t) :
    |External.gammaLogRatioKernel a t| ≤ (a+(1-Real.exp (-r))⁻¹)/r := by
  have ht : 0<t := hr.trans_le hrt
  have hD : 0<1-Real.exp (-r) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hE : 0<1-Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hDE : 1-Real.exp (-r)≤1-Real.exp (-t) := by
    have he := Real.exp_le_exp.mpr (show -t≤-r by linarith)
    linarith
  have hN0 : 0≤1-Real.exp (-a*t) := by
    have he : Real.exp (-a*t)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have hN1 : 1-Real.exp (-a*t)≤1 := by linarith [Real.exp_pos (-a*t)]
  have hQ0 : 0≤(1-Real.exp (-a*t))/(1-Real.exp (-t)) := div_nonneg hN0 hE.le
  have hQ : (1-Real.exp (-a*t))/(1-Real.exp (-t))≤(1-Real.exp (-r))⁻¹ := by
    calc
      _ ≤ 1/(1-Real.exp (-t)) := div_le_div_of_nonneg_right hN1 hE.le
      _ ≤ _ := by simpa only [one_div] using inv_anti₀ hD hDE
  rw [External.gammaLogRatioKernel,abs_div,abs_of_pos ht]
  calc
    _ ≤ (|a|+|(1-Real.exp (-a*t))/(1-Real.exp (-t))|)/t :=
      div_le_div_of_nonneg_right (abs_sub _ _) ht.le
    _ = (a+(1-Real.exp (-a*t))/(1-Real.exp (-t)))/t := by rw [abs_of_pos ha,abs_of_nonneg hQ0]
    _ ≤ (a+(1-Real.exp (-r))⁻¹)/t := div_le_div_of_nonneg_right (add_le_add le_rfl hQ) ht.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hr hrt
lemma gammaRatioKernel_ray_bounded (a r : ℝ) (ha : 0<a) (hr : 0<r) :
    ∃ T : ℝ,0<T ∧ ∀t:ℝ,r≤t → ‖gammaRatioKernel a (t:ℂ)‖≤T := by
  have hD : 0<1-Real.exp (-r) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  refine ⟨(a+(1-Real.exp (-r))⁻¹)/r,by positivity,?_⟩
  intro t ht
  rw [gammaRatioKernel_real a t ha (hr.trans_le ht),Complex.norm_real,Real.norm_eq_abs]
  exact gammaLogRatioKernel_tail_bound a r ha hr t ht
end WP.Analysis
