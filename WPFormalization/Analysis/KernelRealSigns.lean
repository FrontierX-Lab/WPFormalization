import WPFormalization.Analysis.CharacteristicBounds
import WPFormalization.Analysis.StationaryIntegral

/-! Actual signs of the deformed kernel used to construct its real zeros.
The weighted characteristic is strictly decreasing in the parameter, is
negative at sine zeros, and positive at sufficiently large positive sine
midpoints. Direct integral positivity also excludes all nonpositive real
zeros of K. These facts are independent of a complex zero-count theorem. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma weightedCharacteristic_zero_parameter (t : ℝ) (ht : 0 < t) :
    weightedCharacteristic t 0 = Real.sin t := by
  have hs := congrArg Complex.re (rootKernel_sine (t:ℂ))
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    sub_zero,← Complex.ofReal_sin,Complex.ofReal_re] at hs
  unfold weightedCharacteristic
  rw [characteristicIntegral_eq]
  simp only [mul_zero,sub_zero,Complex.ofReal_zero,Real.sqrt_sq_eq_abs,abs_of_pos ht]
  simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat] using hs
lemma weightedCharacteristic_strictAnti (Y t : ℝ) (hY : Y ∈ Ico 0 y₀)
    (ht : 4*Y < t^2) : StrictAntiOn (weightedCharacteristic t) (Icc 0 Y) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (weightedCharacteristic_continuous t).continuousOn
  intro u hu
  have hui : u ∈ Icc 0 Y := interior_subset hu
  have hqu : 0 < t^2-4*u := by linarith [hui.2]
  rw [(weightedCharacteristic_hasDerivAt t u hqu).deriv]
  exact div_neg_of_neg_of_pos (by nlinarith [a_pos u ⟨hui.1,lt_of_le_of_lt hui.2 hY.2⟩])
    (Real.sqrt_pos.2 hqu)
lemma deformedKernel_sine_zero_negative (Y t : ℝ) (hY : Y ∈ Ioo 0 y₀)
    (ht : 0<t) (hext : 4*Y<t^2) (hsin : Real.sin t=0) :
    (K Y (((t^2-4*Y)/2:ℝ):ℂ)).re < 0 := by
  have hanti := weightedCharacteristic_strictAnti Y t ⟨hY.1.le,hY.2⟩ hext
  have hh := hanti ⟨le_rfl,hY.1.le⟩ ⟨hY.1.le,le_rfl⟩ hY.1
  rw [weightedCharacteristic_zero_parameter t ht,hsin] at hh
  unfold weightedCharacteristic at hh
  rw [characteristicIntegral_eq] at hh
  change Real.sqrt (t^2-4*Y)*(K Y (((t^2-4*Y)/2:ℝ):ℂ)).re < 0 at hh
  nlinarith only [hh,Real.sqrt_pos.2 (sub_pos.mpr hext)]
lemma complex_sqrt_ofReal (x : ℝ) (hx : 0 ≤ x) :
    Complex.sqrt (x:ℂ) = (Real.sqrt x:ℂ) := by
  rw [Complex.sqrt,Real.sqrt_eq_rpow,Complex.ofReal_cpow hx]
  norm_num
lemma characteristicRoot_real_pos (Y t : ℝ) (_hY : 0≤Y) (ht : 0<t)
    (hext : 4*Y<t^2) :
    characteristicRoot (t:ℂ) (Y:ℂ) = (Real.sqrt (1-4*Y/t^2):ℂ) ∧
      0<Real.sqrt (1-4*Y/t^2) := by
  have ht2 : 0<t^2 := sq_pos_of_pos ht
  have hp : 0<1-4*Y/t^2 := by rw [sub_pos,div_lt_one ht2];exact hext
  constructor
  · unfold characteristicRoot
    rw [show (1-4*(Y:ℂ)/(t:ℂ)^2) = ((1-4*Y/t^2:ℝ):ℂ) by push_cast;ring]
    exact complex_sqrt_ofReal _ hp.le
  · exact Real.sqrt_pos.2 hp
lemma K_nonpositive_re_pos (Y z : ℝ) (hY : Y<y₀) (hz : z≤0) :
    0<(K Y z).re := by
  rw [K_real_integral]
  apply intervalIntegral.integral_pos zero_lt_one
  · have hc : Continuous a := by
      unfold a
      have hd : Continuous (deriv X) := by
        simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
      exact Complex.continuous_re.comp (hd.comp Complex.continuous_ofReal)
    exact (hc.comp (by fun_prop)).continuousOn
  · intro s hs
    have hfac : 0≤1-s^2 := by nlinarith [hs.1,hs.2]
    exact (a_pos_before_y₀ _ (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hz hfac])).le
  · refine ⟨1,⟨zero_le_one,le_rfl⟩,?_⟩
    simpa using a_pos_before_y₀ Y hY
lemma characteristicCorrection_norm_le_midpoint (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (t : ℂ)
    (ht : (7:ℝ)≤‖t‖) : ‖characteristicCorrection Y t‖≤(1/2:ℝ) := by
  have hYmax : Y≤3/2 := hY.2.trans y₀_lt_three_halves.le
  have ht2 : (49:ℝ)≤‖t‖^2 := by nlinarith
  have hext : 4*Y<‖t‖^2 := by linarith
  have hsqrt : (6:ℝ)≤Real.sqrt (‖t‖^2-4*Y) := by
    exact (Real.le_sqrt (by norm_num : (0:ℝ)≤6) (by linarith)).2 (by nlinarith)
  have hXR := XR_le_self_interval Y ⟨hY.1,by linarith⟩
  calc
    _ ≤ 2*XR Y/Real.sqrt (‖t‖^2-4*Y) := characteristicCorrection_norm_le Y hY t hext
    _ ≤ (1/2:ℝ) := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<6) hsqrt)).2
      nlinarith
lemma deformedKernel_sine_one_positive (Y t : ℝ) (hY : Y∈Icc 0 y₀)
    (ht : (7:ℝ)≤t) (hsin : Real.sin t=1) :
    0<(K Y (((t^2-4*Y)/2:ℝ):ℂ)).re := by
  have ht0 : 0<t := lt_of_lt_of_le (by norm_num) ht
  have ht2 : (49:ℝ)≤t^2 := by nlinarith
  have hext : 4*Y<t^2 := by linarith [hY.2,y₀_lt_three_halves]
  have htc : ‖(t:ℂ)‖=t := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
  have hq := characteristicRoot_real_pos Y t hY.1 ht0 hext
  have hid := congrArg Complex.re (complex_characteristic_identity Y hY.1 (t:ℂ)
    (by rwa [htc]))
  rw [hq.1] at hid
  have harg : ((t:ℂ)^2-4*(Y:ℂ))/2 = (((t^2-4*Y)/2:ℝ):ℂ) := by push_cast;ring
  rw [harg] at hid
  change (((t:ℂ)*(Real.sqrt (1-4*Y/t^2):ℂ))*K Y (((t^2-4*Y)/2:ℝ):ℂ)).re =
    (Complex.sin (t:ℂ)-characteristicCorrection Y t).re at hid
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
    sub_zero,Complex.mul_im,add_zero,Complex.sub_re,←Complex.ofReal_sin] at hid
  rw [hsin] at hid
  have hc := characteristicCorrection_norm_le_midpoint Y hY (t:ℂ) (by rwa [htc])
  have hre := (le_abs_self (characteristicCorrection Y (t:ℂ)).re).trans
    (Complex.abs_re_le_norm _)
  nlinarith [mul_pos ht0 hq.2]
end WP.Analysis
