import WPFormalization.Analysis.CharacteristicBounds
import WPFormalization.Analysis.SqrtPerturbation
import WPFormalization.Analysis.SineCircleBounds

/-! The explicit Rouche boundary estimate for the actual deformed kernel.
On every half-integer pi circle of radius at least 100, the actual kernel
perturbation is strictly smaller than the sine reference. All numerical
estimates and the characteristic identity are proved locally; this file
assumes no zero-count theorem and no deformed-kernel root classification. -/
noncomputable section
namespace WP.Analysis
open Set
lemma characteristicCorrection_norm_le_large (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (t : ℂ)
    (ht : (100:ℝ) ≤ ‖t‖) : ‖characteristicCorrection Y t‖ ≤ (1/25:ℝ) := by
  have hYmax : Y ≤ 3/2 := hY.2.trans y₀_lt_three_halves.le
  have ht2 : (10000:ℝ) ≤ ‖t‖^2 := by nlinarith
  have hext : 4*Y < ‖t‖^2 := by linarith
  have hsqrt : (75:ℝ) ≤ Real.sqrt (‖t‖^2-4*Y) := by
    apply (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 75) (by linarith : 0 ≤ ‖t‖^2-4*Y)).2
    nlinarith
  have hXR : XR Y ≤ Y := XR_le_self_interval Y ⟨hY.1,by linarith⟩
  calc
    _ ≤ 2*XR Y/Real.sqrt (‖t‖^2-4*Y) := characteristicCorrection_norm_le Y hY t hext
    _ ≤ (1/25:ℝ) := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<75) hsqrt)).2
      nlinarith
lemma characteristic_normalized_perturbation (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (t : ℂ)
    (ht : (100:ℝ) ≤ ‖t‖) :
    ‖(characteristicRoot t Y)⁻¹‖ ≤ 2 ∧
      ‖(characteristicRoot t Y)⁻¹-1‖ ≤ (1/50:ℝ) := by
  let w : ℂ := 4*(Y:ℂ)/t^2
  have hYmax : Y ≤ 3/2 := hY.2.trans y₀_lt_three_halves.le
  have ht2 : (10000:ℝ) ≤ ‖t‖^2 := by nlinarith
  have hw : ‖w‖ ≤ (1/100:ℝ) := by
    dsimp [w]
    rw [norm_div,norm_mul,norm_pow]
    norm_num only [Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg hY.1]
    apply (div_le_iff₀ (by linarith : 0 < ‖t‖^2)).2
    nlinarith
  have hw' : ‖w‖ ≤ (1/2:ℝ) := hw.trans (by norm_num)
  exact ⟨complex_sqrt_inverse_norm w hw',
    (complex_sqrt_inverse_sub_one_norm w hw').trans (by linarith)⟩
lemma kernel_rouche_boundary (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (N : ℕ) (hN : (100:ℝ) ≤ ((N:ℝ)+1/2)*Real.pi)
    (t : ℂ) (ht : ‖t‖ = ((N:ℝ)+1/2)*Real.pi) :
    ‖K Y ((t^2-4*Y)/2)-K 0 (t^2/2)‖ < ‖K 0 (t^2/2)‖ := by
  have htlarge : (100:ℝ) ≤ ‖t‖ := ht.symm ▸ hN
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le (by norm_num) htlarge
  have ht0 : t ≠ 0 := norm_pos_iff.mp htpos
  have hext : 4*Y < ‖t‖^2 := by
    have hYmax : Y ≤ 3/2 := hY.2.trans y₀_lt_three_halves.le
    nlinarith
  let q := characteristicRoot t Y
  let c := characteristicCorrection Y t
  have hq : q ≠ 0 := characteristicRoot_ne_zero t Y
    (characteristic_slit_of_norm Y hY.1 t hext Y ⟨hY.1,le_rfl⟩)
  have hid := complex_characteristic_identity Y hY.1 t hext
  have hsine : t*K 0 (t^2/2) = Complex.sin t := by
    simpa only [K,rootKernel] using rootKernel_sine t
  have he : t*(K Y ((t^2-4*Y)/2)-K 0 (t^2/2)) =
      (q⁻¹-1)*Complex.sin t-q⁻¹*c := by
    change t*q*K Y ((t^2-4*Y)/2) = Complex.sin t-c at hid
    field_simp
    linear_combination hid-q*hsine
  have hb := characteristic_normalized_perturbation Y hY t htlarge
  have hc := characteristicCorrection_norm_le_large Y hY t htlarge
  have hsin := complex_sin_circle_lower N t ht
  have hnorm : ‖t*(K Y ((t^2-4*Y)/2)-K 0 (t^2/2))‖ < ‖Complex.sin t‖ := by
    rw [he]
    calc
      _ ≤ ‖q⁻¹-1‖*‖Complex.sin t‖+‖q⁻¹‖*‖c‖ := by
        simpa only [norm_mul] using norm_sub_le ((q⁻¹-1)*Complex.sin t) (q⁻¹*c)
      _ ≤ (1/50:ℝ)*‖Complex.sin t‖+2*(1/25:ℝ) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _))
          (mul_le_mul hb.1 hc (norm_nonneg _) (by norm_num))
      _ < ‖Complex.sin t‖ := by linarith
  rw [norm_mul,← hsine,norm_mul] at hnorm
  exact (mul_lt_mul_iff_right₀ htpos).mp hnorm
end WP.Analysis
