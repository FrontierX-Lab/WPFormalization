import WPFormalization.JT.AbelStatement
import WPFormalization.JT.AbelSubstitution

/-! Exact conversion of the real Abel integral to the existing entire K. -/
noncomputable section
namespace WP.JT
open MeasureTheory

lemma kernel_real_integral (Y z : ℝ) :
    (K (Y : ℂ) (z : ℂ)).re =
      ∫ s : ℝ in (0)..1, a (Y + z/2*(1-s^2)) := by
  have he (s : ℝ) :
      deriv X ((Y : ℂ) + (z : ℂ)/2*(1-(s : ℂ)^2)) =
        (a (Y + z/2*(1-s^2)) : ℂ) := by
    have ha : (Y : ℂ) + (z : ℂ)/2*(1-(s : ℂ)^2) =
        ((Y + z/2*(1-s^2) : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, derivX_ofReal]
  simp only [K, he, intervalIntegral.integral_ofReal, Complex.ofReal_re]

lemma abel_density_kernel (Y q : ℝ) (hq : 0 ≤ q) :
    abelDensity Y (edgeEnergy Y + q) =
      Real.sqrt q / (2 * Real.pi) *
        (K (Y : ℂ) ((-2 * Real.pi^2 * q : ℝ) : ℂ)).re := by
  unfold abelDensity
  rw [abel_substitution besselI0Energy besselI0Energy_continuous _ _ hq,
    kernel_real_integral]
  have he (s : ℝ) : besselI0Energy (edgeEnergy Y + q*(1-s^2)) =
      a (Y + (-2 * Real.pi^2 * q)/2*(1-s^2)) := by
    rw [besselI0Energy_eq_a]
    congr 1
    unfold edgeEnergy
    field_simp
    ring
  simp_rw [he]
  ring

/-- No imaginary component is discarded in the real density formula. -/
lemma abel_density_kernel_complex (Y q : ℝ) (hq : 0 ≤ q) :
    (abelDensity Y (edgeEnergy Y + q) : ℂ) =
      ((Real.sqrt q / (2 * Real.pi) : ℝ) : ℂ) *
        K (Y : ℂ) ((-2 * Real.pi^2 * q : ℝ) : ℂ) := by
  have hr := abel_density_kernel Y q hq
  apply Complex.ext
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hr
  · have hi : (K (Y : ℂ) ((-2 * Real.pi^2 * q : ℝ) : ℂ)).im = 0 := by
      exact Analysis.rootKernel_real Y (-2 * Real.pi^2 * q)
    simp only [Complex.mul_im, Complex.ofReal_im, hi, mul_zero, zero_mul, add_zero]

lemma abel_density_intervalIntegrable (Y E : ℝ) (hE : edgeEnergy Y ≤ E) :
    IntervalIntegrable (fun u => besselI0Energy u / Real.sqrt (E-u))
      volume (edgeEnergy Y) E := by
  have h := abel_intervalIntegrable besselI0Energy besselI0Energy_continuous
    (edgeEnergy Y) (E-edgeEnergy Y) (sub_nonneg.mpr hE)
  simpa only [add_sub_cancel] using h

lemma abel_density_kernel_at (Y E : ℝ) (hE : edgeEnergy Y ≤ E) :
    abelDensity Y E = Real.sqrt (E-edgeEnergy Y) / (2 * Real.pi) *
      (K (Y : ℂ) ((-2 * Real.pi^2 * (E-edgeEnergy Y) : ℝ) : ℂ)).re := by
  simpa only [add_sub_cancel] using abel_density_kernel Y (E-edgeEnergy Y) (sub_nonneg.mpr hE)

lemma abel_density_edge (Y : ℝ) : abelDensity Y (edgeEnergy Y) = 0 := by
  simp [abelDensity]

end WP.JT
