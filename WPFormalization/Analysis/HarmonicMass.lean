import WPFormalization.Analysis.FormalMass
import WPFormalization.Analysis.KernelJets
import WPFormalization.Analysis.HarmonicPositivity
import WPFormalization.Intersection.ShiftedRecursion

/-! The harmonic mass identity for the actual analytic kernels.
The finite coefficient algebra is proved here; strict positivity is provided
by harmonicCoeff_pos, whose remaining kernel assumptions are audited upstream.
-/
noncomputable section
namespace WP.Analysis
open PowerSeries

lemma barK_zero_closed (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) : barK Y 0 = 1 := by
  by_cases he : Y = y₀
  · simp [barK, he]
  · exact barK_zero Y ⟨hY.1, lt_of_le_of_ne hY.2 he⟩

lemma realTaylor_kernel_identity (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    realTaylor (barK Y) = realTaylor (barH Y)+C (2/3 : ℝ)*PowerSeries.X*
      PowerSeries.derivative (realTaylor (barH Y)) := by
  have hf := (barH_differentiable Y).analyticAt 0
  have hg : AnalyticAt ℂ (fun z : ℂ => ((2/3 : ℝ) : ℂ)*(z*deriv (barH Y) z)) 0 :=
    analyticAt_const.mul (analyticAt_id.mul hf.deriv)
  have he : barK Y = fun z : ℂ => barH Y z+((2/3 : ℝ) : ℂ)*(z*deriv (barH Y) z) := by
    funext z
    rw [normalized_kernel_identity Y hY z]
    norm_num
    ring
  rw [he, realTaylor_add (f := barH Y) (g := fun z : ℂ => ((2/3 : ℝ) : ℂ)*(z*deriv (barH Y) z)) hf hg,
    realTaylor_const_mul, realTaylor_euler hf]
  ring

lemma theta_eq_formal_inverse (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (m : ℕ) :
    theta Y m = PowerSeries.coeff m (realTaylor (barK Y))⁻¹ := by
  rw [← realTaylor_inv ((barK_differentiable Y).analyticAt 0)
    (by rw [barK_zero_closed Y hY]; norm_num) (barK_realCoefficients Y)]
  simp only [realTaylor_coeff, theta]

lemma harmonicCoeff_eq_formal (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (h m : ℕ) :
    harmonicCoeff Y h m = PowerSeries.coeff m ((realTaylor (barH Y))⁻¹^h) := by
  have hf := (barH_differentiable Y).analyticAt 0
  have hzero : barH Y 0 ≠ 0 := by rw [barH_zero Y hY]; norm_num
  have hr := barH_realCoefficients Y
  rw [← realTaylor_inv hf hzero hr, ← realTaylor_pow (f := fun z => (barH Y z)⁻¹) (hf.inv hzero)
    (realCoefficients_inv hf hzero hr) h]
  simp only [realTaylor_coeff, harmonicCoeff]

/-- Eq.4.12 before dividing by A_m(h); this part uses no positivity input. -/
theorem harmonic_mass_numerator (Y : ℝ) (h m : ℕ) (hh : 2 ≤ h)
    (hY : Y ∈ Set.Icc 0 y₀) :
    (∑ l ∈ Finset.range (m+1), theta Y l*harmonicCoeff Y (h-1) (m-l)*
      (1-2*((m : ℝ)-l)/(3*((h : ℝ)-1)))) = harmonicCoeff Y h m := by
  have hf : constantCoeff (realTaylor (barH Y)) ≠ 0 := by
    rw [realTaylor_constant, barH_zero Y hY]; norm_num
  have hk : constantCoeff (realTaylor (barK Y)) ≠ 0 := by
    rw [realTaylor_constant, barK_zero_closed Y hY]; norm_num
  have he := formal_mass_coefficients (realTaylor (barH Y)) (realTaylor (barK Y))
    hf hk (realTaylor_kernel_identity Y hY) h m hh
  rw [harmonicCoeff_eq_formal Y hY h m]
  convert he using 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlm : l ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  rw [theta_eq_formal_inverse Y hY, harmonicCoeff_eq_formal Y hY,
    Nat.cast_sub hlm]

/-- The actual normalized harmonic mass, with the denominator justified. -/
theorem harmonic_mass_identity (Y : ℝ) (h m : ℕ) (hh : 2 ≤ h)
    (hY : Y ∈ Set.Icc 0 y₀) :
    ∑ l ∈ Finset.range (m+1),
      (theta Y l*harmonicCoeff Y (h-1) (m-l)/harmonicCoeff Y h m)*
        (1-2*((m : ℝ)-l)/(3*((h : ℝ)-1))) = 1 := by
  have hden : harmonicCoeff Y h m ≠ 0 := (harmonicCoeff_pos Y h m (by omega) hY).ne'
  calc
    _ = (∑ l ∈ Finset.range (m+1), theta Y l*harmonicCoeff Y (h-1) (m-l)*
        (1-2*((m : ℝ)-l)/(3*((h : ℝ)-1))))/harmonicCoeff Y h m := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = 1 := by rw [harmonic_mass_numerator Y h m hh hY, div_self hden]

end WP.Analysis
