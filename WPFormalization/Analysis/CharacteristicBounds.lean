import WPFormalization.Analysis.ComplexCharacteristic
import WPFormalization.Analysis.CriticalBesselData
/-! A uniform exterior bound for the actual characteristic correction.
The bound follows from the exact characteristic identity, the reverse triangle
inequality for its square root, positivity of a on the actual parameter segment,
and the proved integral of a. No kernel zero enumeration is assumed. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology

lemma characteristic_denominator_lower (Y : ℝ) (hY : 0 ≤ Y) (t : ℂ)
    (ht : 4*Y < ‖t‖^2) (u : ℝ) (hu : u ∈ Icc 0 Y) :
    Real.sqrt (‖t‖^2-4*Y) ≤ ‖t*characteristicRoot t u‖ := by
  have ht0 : t ≠ 0 := by
    intro he
    simp only [he,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at ht
    linarith
  have hsq : ‖t*characteristicRoot t u‖^2 = ‖t^2-4*(u:ℂ)‖ := by
    rw [← norm_pow,mul_pow,characteristicRoot_sq t u ht0]
  apply (Real.sqrt_le_left (norm_nonneg _)).2
  rw [hsq]
  have hh : ‖t‖^2-4*u ≤ ‖t^2-4*(u:ℂ)‖ := by
    have hh := norm_sub_norm_le (t^2) (4*(u:ℂ))
    rw [norm_pow t 2] at hh
    simpa only [norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hu.1] using hh
  exact (show ‖t‖^2-4*Y ≤ ‖t‖^2-4*u by linarith [hu.2]).trans hh
private lemma a_nonneg_on_segment (u : ℝ) (hu : u ∈ Icc 0 y₀) : 0 ≤ a u := by
  by_cases he : u = y₀
  · subst u
    rw [a_y₀_zero]
  · exact (a_pos u ⟨hu.1,lt_of_le_of_ne hu.2 he⟩).le
private lemma a_cont_for_characteristic : Continuous a := by
  unfold a
  have hd : Continuous (deriv X) := by
    simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
  exact Complex.continuous_re.comp (hd.comp Complex.continuous_ofReal)
lemma integral_a_characteristic (Y : ℝ) : (∫ u : ℝ in (0)..Y, a u) = XR Y := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=Y)
    (fun u _ => XR_hasDerivAt u) (a_cont_for_characteristic.intervalIntegrable 0 Y)
  simpa only [XR_zero,sub_zero] using h

def characteristicCorrection (Y : ℝ) (t : ℂ) : ℂ :=
  2*(∫ u : ℝ in (0)..Y, deriv X u/(t*characteristicRoot t u))
lemma characteristicCorrection_norm_le (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (t : ℂ)
    (ht : 4*Y < ‖t‖^2) :
    ‖characteristicCorrection Y t‖ ≤ 2*XR Y/Real.sqrt (‖t‖^2-4*Y) := by
  let d : ℝ := Real.sqrt (‖t‖^2-4*Y)
  have hd : 0 < d := Real.sqrt_pos.2 (sub_pos.mpr ht)
  have hb (u : ℝ) (hu : u ∈ Icc 0 Y) :
      ‖deriv X u/(t*characteristicRoot t u)‖ ≤ a u/d := by
    have ha := a_nonneg_on_segment u ⟨hu.1,hu.2.trans hY.2⟩
    have he : ‖deriv X (u:ℂ)‖ = a u := by
      rw [derivX_ofReal]
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
    rw [norm_div,he]
    exact div_le_div_of_nonneg_left ha hd (characteristic_denominator_lower Y hY.1 t ht u hu)
  have hi : ‖∫ u : ℝ in (0)..Y, deriv X u/(t*characteristicRoot t u)‖ ≤ XR Y/d := by
    calc
      _ ≤ ∫ u : ℝ in (0)..Y, a u/d := by
        apply intervalIntegral.norm_integral_le_of_norm_le hY.1
        · filter_upwards with u hu
          exact hb u ⟨hu.1.le,hu.2⟩
        · exact (a_cont_for_characteristic.div_const d).intervalIntegrable 0 Y
      _ = XR Y/d := by rw [intervalIntegral.integral_div,integral_a_characteristic]
  change ‖(2:ℂ)*(∫ u : ℝ in (0)..Y, deriv X u/(t*characteristicRoot t u))‖ ≤ _
  rw [norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ 2*(XR Y/d) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by dsimp [d];ring
end WP.Analysis
