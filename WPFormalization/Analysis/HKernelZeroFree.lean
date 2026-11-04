import WPFormalization.Analysis.FirstKernelRoot
import WPFormalization.Analysis.HKernelPositivity
import WPFormalization.Analysis.CoefficientScaling
import WPFormalization.External.Pringsheim
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma H_integral_K (Y z : ℂ) : H Y z = 3*∫ t : ℝ in (0)..1, (t:ℂ)^2*K Y (z*(t:ℂ)^2) := by
  have hc : Continuous (fun t:ℝ => 3*(t:ℂ)^2*K Y (z*(t:ℂ)^2)) := by
    have hK := (K_differentiable Y).continuous
    fun_prop
  have hd (t:ℝ) : HasDerivAt (fun t:ℝ => (t:ℂ)^3*H Y (z*(t:ℂ)^2))
      (3*(t:ℂ)^2*K Y (z*(t:ℂ)^2)) t := by
    have ht : HasDerivAt (fun t:ℝ => (t:ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have hh := (H_differentiable Y (z*(t:ℂ)^2)).hasDerivAt.comp t ((ht.pow 2).const_mul z)
    convert (ht.pow 3).mul hh using 1
    · rfl
    · rw [kernel_differential]
      norm_num
      ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simp only [Complex.ofReal_one,Complex.ofReal_zero,one_pow,zero_pow (by decide : 3≠0),one_mul,mul_one,zero_mul,sub_zero] at he
  simp_rw [mul_assoc] at he
  rw [intervalIntegral.integral_const_mul] at he
  exact he.symm
lemma K_re_nonneg_to_r (Y:ℝ)(hY:Y∈Ico 0 y₀)(z:ℝ)(hz:z∈Icc 0 (r Y)) : 0≤(K Y z).re := by
  have hr := K_r_zero Y hY
  have hh := (K_strictAntiOn_interval Y hY.1).antitoneOn
    ⟨hz.1,hz.2.trans (r_le_pi Y hY)⟩ ⟨(r_pos Y hY).le,r_le_pi Y hY⟩ hz.2
  simpa only [hr,Complex.zero_re] using hh
lemma K_re_pos_before_r (Y:ℝ)(hY:Y∈Ico 0 y₀)(z:ℝ)(hz:z∈Ico 0 (r Y)) : 0<(K Y z).re := by
  have hr := K_r_zero Y hY
  have hh := (K_strictAntiOn_interval Y hY.1)
    ⟨hz.1,hz.2.le.trans (r_le_pi Y hY)⟩ ⟨(r_pos Y hY).le,r_le_pi Y hY⟩ hz.2
  simpa only [hr,Complex.zero_re] using hh
lemma H_re_pos_to_r (Y:ℝ)(hY:Y∈Ico 0 y₀)(z:ℝ)(hz:z∈Icc 0 (r Y)) : 0<(H Y z).re := by
  let f (t:ℝ):ℂ := (t:ℂ)^2*K Y ((z:ℂ)*(t:ℂ)^2)
  have hc : Continuous f := by
    have hK := (K_differentiable Y).continuous
    dsimp [f]
    fun_prop
  have hf (t:ℝ) : (f t).re = t^2*(K Y ((z*t^2:ℝ):ℂ)).re := by
    have he : f t = ((t^2:ℝ):ℂ)*K Y ((z*t^2:ℝ):ℂ) := by dsimp [f]; push_cast; rfl
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have harg (t:ℝ)(ht:t∈Icc 0 1) : z*t^2 ∈ Icc 0 (r Y) := by
    have ht2 : t^2≤1 := by nlinarith [ht.1,ht.2]
    exact ⟨mul_nonneg hz.1 (sq_nonneg t),le_trans (by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr ht2)]) hz.2⟩
  have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num : (0:ℝ)<1)
    continuous_const.continuousOn (Complex.continuous_re.comp hc).continuousOn
    (f := fun _ => (0:ℝ)) (fun t ht => by
      change 0≤(f t).re
      rw [hf]
      exact mul_nonneg (sq_nonneg t) (K_re_nonneg_to_r Y hY _ (harg t ⟨ht.1.le,ht.2⟩)))
    ⟨1/2,by norm_num,by
      change 0<(f (1/2)).re
      rw [hf]
      apply mul_pos (by norm_num)
      apply K_re_pos_before_r Y hY
      constructor
      · exact mul_nonneg hz.1 (sq_nonneg _)
      · nlinarith [r_pos Y hY,hz.1,hz.2]⟩
  rw [intervalIntegral.integral_zero] at hh
  rw [H_integral_K]
  change 0<(3*(∫ t:ℝ in (0)..1,f t)).re
  rw [Complex.mul_re]
  norm_num
  have he := intervalIntegral.intervalIntegral_re (hc.intervalIntegrable (μ := volume) 0 1)
  change (∫ t:ℝ in (0)..1, (f t).re) = (∫ t:ℝ in (0)..1, f t).re at he
  change 0<(∫ t:ℝ in (0)..1, (f t).re) at hh
  rw [he] at hh
  linarith
lemma H_realCoefficients_ofReal (Y:ℝ) : RealCoefficients (H Y) := by
  intro n
  rw [coeff_H_formula]
  simp [Complex.div_im,Complex.mul_im,iteratedDeriv_X_im_ofReal]
lemma H_inverse_coeff_pos (Y:ℝ)(hY:Y∈Ico 0 y₀)(n:ℕ) : 0<(WP.coeff (fun z=>(H Y z)⁻¹) n).re := by
  have hh := H_negative_power_coeff_pos Y hY 1 zero_lt_one n
  have he := realCoeff_inv_pow_eq_exp (H Y) (H_differentiable Y).continuous.continuousAt
    (show H Y 0≠0 by rw [H_zero,derivX_ofReal]; exact_mod_cast a_ne_zero Y hY) 1 n
  norm_num only [pow_one,Nat.cast_one,Complex.ofReal_one] at he hh
  change 0<realCoeff (fun z=>(H Y z)⁻¹) n
  rw [he]
  exact hh
lemma H_zero_free_closed_disk (Y:ℝ)(hY:Y∈Ico 0 y₀) : ∀ z:ℂ, ‖z‖≤r Y → H Y z≠0 := by
  apply External.zero_free_disk_of_nonnegative_inverseCoefficients _ (H_differentiable Y) (r Y) (r_pos Y hY).le
  · have hr := realCoefficients_inv ((H_differentiable Y).analyticAt 0)
      (show H Y 0≠0 by rw [H_zero,derivX_ofReal]; exact_mod_cast a_ne_zero Y hY)
      (H_realCoefficients_ofReal Y)
    exact fun n => ⟨hr n,(H_inverse_coeff_pos Y hY n).le⟩
  · intro x hx he
    have hp := H_re_pos_to_r Y hY x hx
    rw [he] at hp
    exact (lt_irrefl 0) hp
end WP.Analysis
