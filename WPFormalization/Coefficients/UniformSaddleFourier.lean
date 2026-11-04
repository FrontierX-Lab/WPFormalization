import WPFormalization.Coefficients.UniformSaddleProbability
import WPFormalization.Coefficients.UniformSaddleMeanBounds
import WPFormalization.Analysis.PositiveSeriesCharacteristic
import WPFormalization.Analysis.ScaledFourierTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Fourier. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
open WP.Analysis
lemma unscaledCoeff_one_one : unscaledCoeff 1 1=1/5:=by
  have hH0:H 0 0=1:=by rw[H_zero,Analysis.derivX_zero]
  have hd:=((H_differentiable 0 0).hasDerivAt.inv (by rw[hH0];exact one_ne_zero)).deriv
  have he:deriv (fun w:ℂ=>(H 0 w)⁻¹) 0=kernelLogSlope 0:=by
    change deriv (H 0)⁻¹ 0=kernelLogSlope 0
    rw[hd]
    simp only[kernelLogSlope,hH0,one_pow,div_one]
  simp only[unscaledCoeff,pow_one,realCoeff,WP.coeff,Nat.factorial_one,Nat.cast_one,
    div_one,iteratedDeriv_one,he,kernelLogSlope_zero]
  norm_num
lemma tiltedKernelPower_coeff_complex (z:ℝ)(h m:ℕ):
    WP.coeff (fun w:ℂ=>(tiltedKernelPGF z w)^h) m=(tiltedKernelMass z h m:ℂ):=by
  have he:(fun w:ℂ=>(tiltedKernelPGF z w)^h)=
      (fun w:ℂ=>((H 0 z).re:ℂ)^h*(H 0 ((z:ℂ)*w))⁻¹^h):=by
    funext w
    rw[tiltedKernelPGF,div_pow,div_eq_mul_inv,H_zero_real z]
    simp only[inv_pow,Complex.ofReal_re]
  rw[he,coeff_const_mul]
  have hscale:WP.coeff (fun w:ℂ=>(H 0 ((z:ℂ)*w))⁻¹^h) m=
      (z:ℂ)^m*WP.coeff (fun w:ℂ=>(H 0 w)⁻¹^h) m:=by
    unfold WP.coeff
    rw[iteratedDeriv_comp_mul_left (fun w:ℂ=>(H 0 w)⁻¹^h),mul_zero]
    ring
  rw[hscale,unscaledCoeff_complex,tiltedKernelMass_eq_unscaled]
  push_cast
  ring
lemma tiltedKernelPower_analytic_radius (z:ℝ)(hz:0<z)(hzr:z≤ r 0)(h:ℕ):
    ∃R:ℝ,1<R∧AnalyticOnNhd ℂ (fun w:ℂ=>(tiltedKernelPGF z w)^h) (Metric.ball 0 R):=by
  obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
  refine ⟨R/z,(one_lt_div hz).mpr (hzr.trans_lt hR),?_⟩
  intro w hw
  have hn:‖(z:ℂ)*w‖<R:=by
    rw[norm_mul,Complex.norm_of_nonneg hz.le]
    exact (mul_comm z ‖w‖ ▸ (lt_div_iff₀ hz).mp
      (by simpa only[Metric.mem_ball,dist_zero_right] using hw))
  have ha:AnalyticAt ℂ (fun w:ℂ=>H 0 ((z:ℂ)*w)) w:=
    ((H_differentiable 0).analyticAt _).comp (by fun_prop)
  exact (analyticAt_const.div ha (hzero _ hn.le)).pow h
lemma tiltedKernelPower_characteristic_bound :
    ∃c:ℝ,0<c∧∀z∈Icc (0:ℝ) (r 0),∀h:ℕ,∀θ:ℝ,|θ|≤ Real.pi→
      ‖(tiltedKernelPGF z (Complex.exp ((θ:ℂ)*Complex.I)))^h‖≤
        Real.exp (-c*(h:ℝ)*z*θ^2):=by
  have hr:0<r 0:=r_pos 0 ⟨le_rfl,y₀_pos⟩
  have hc:ContinuousOn (fun z:ℝ=>(H 0 z).re) (Icc (0:ℝ) (r 0)):=
    (Complex.continuous_re.comp ((H_differentiable 0).continuous.comp Complex.continuous_ofReal)).continuousOn
  obtain ⟨z₀,hz₀,hmin⟩:=isCompact_Icc.exists_isMinOn ⟨0,⟨le_rfl,hr.le⟩⟩ hc
  let a:ℝ:=(H 0 z₀).re
  have ha:0<a:=H_zero_re_pos z₀ hz₀
  let c:ℝ:=2*a^2/(5*Real.pi^2)
  have hc0:0<c:=by dsimp[c];positivity
  refine ⟨c,hc0,?_⟩
  intro z hz h θ hθ
  let w:ℂ:=(z:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  have hw:‖w‖=z:=by
    dsimp[w]
    rw[norm_mul,Complex.norm_of_nonneg hz.1,Complex.norm_exp]
    simp
  have hH:0<(H 0 z).re:=H_zero_re_pos z hz
  have hsumC:=unscaledCoeff_hasSum 1 w (hw.trans_le hz.2)
  simp only[pow_one] at hsumC
  have hsumR:HasSum (fun m:ℕ=>unscaledCoeff 1 m*z^m) (H 0 z).re⁻¹:=by
    have hs:=Complex.hasSum_re (unscaledCoeff_hasSum 1 (z:ℂ)
      (by rw[Complex.norm_of_nonneg hz.1];exact hz.2))
    convert hs using 1
    · ext m
      simp only[←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    · rw[pow_one,H_zero_real z,←Complex.ofReal_inv,Complex.ofReal_re]
      simp only[Complex.ofReal_re]
  have hch:=PositiveConvolution.positive_series_character_exp_bound (unscaledCoeff 1) z hz.1
    (fun m=>(unscaledCoeff_pos 1 m (by omega)).le) w ((H 0 w)⁻¹) ((H 0 z).re⁻¹)
    (inv_pos.mpr hH) hw hsumC hsumR
  rw[unscaledCoeff_zero,unscaledCoeff_one_one] at hch
  have he:‖tiltedKernelPGF z (Complex.exp ((θ:ℂ)*Complex.I))‖=
      ‖(H 0 w)⁻¹‖/(H 0 z).re⁻¹:=by
    rw[tiltedKernelPGF,div_eq_mul_inv,norm_mul,H_zero_real z,Complex.norm_of_nonneg hH.le]
    dsimp[w]
    field_simp
  have hre:w.re=z*Real.cos θ:=by simp[w,Complex.mul_re,Complex.mul_im,Complex.exp_re]
  have hzmin:a≤(H 0 z).re:=hmin hz
  have hcos:2/Real.pi^2*θ^2≤1-Real.cos θ:=by linarith[Real.cos_le_one_sub_mul_cos_sq hθ]
  have hcos0:0≤1-Real.cos θ:=by linarith[Real.cos_le_one θ]
  have hexc:c*z*θ^2≤1*(1/5)*(z-w.re)/((H 0 z).re⁻¹)^2:=by
    rw[hre,inv_pow,div_inv_eq_mul]
    dsimp[c]
    have hs:a^2≤(H 0 z).re^2:=sq_le_sq₀ ha.le hH.le |>.mpr hzmin
    have hz0:=hz.1
    have hm:=mul_le_mul_of_nonneg_left hcos (by positivity:0≤ a^2*z/5)
    have ht:=mul_le_mul_of_nonneg_right hs (by positivity:0≤ z*(1-Real.cos θ)/5)
    calc
      _ = a^2*z/5*(2/Real.pi^2*θ^2):=by ring
      _ ≤ a^2*z/5*(1-Real.cos θ):=hm
      _ = a^2*(z*(1-Real.cos θ)/5):=by ring
      _ ≤ (H 0 z).re^2*(z*(1-Real.cos θ)/5):=ht
      _ = _:=by ring
  have hbase:‖tiltedKernelPGF z (Complex.exp ((θ:ℂ)*Complex.I))‖≤ Real.exp (-c*z*θ^2):=by
    rw[he]
    exact hch.trans (Real.exp_le_exp.mpr (by linarith[hexc]))
  rw[norm_pow]
  apply (pow_le_pow_left₀ (norm_nonneg _) hbase h).trans_eq
  rw[←Real.exp_nat_mul]
  congr 1
  ring
end WP.Coefficients
namespace WP.Coefficients
open Set Filter MeasureTheory
open scoped Topology
open WP.Analysis

def tiltedKernelVariance (z:ℝ):ℝ:=z*deriv unscaledMean z
def scaledTiltedKernelFourier (z:ℝ)(h:ℕ):ℝ→ℂ:=
  scaledCenteredFourier (fun w:ℂ=>(tiltedKernelPGF z w)^h)
    ((h:ℝ)*unscaledMean z) (Real.sqrt ((h:ℝ)*tiltedKernelVariance z))
lemma tiltedKernelVariance_pos (z:ℝ)(hz:0<z)(hzr:z≤ r 0):0<tiltedKernelVariance z:=by
  exact mul_pos hz (lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (unscaledMean_deriv_lower z ⟨hz.le,hzr⟩))
lemma scaledTiltedKernelFourier_integrable (z:ℝ)(hz:0<z)(hzr:z≤ r 0)(h:ℕ):
    Integrable (scaledTiltedKernelFourier z h):=by
  obtain ⟨R,hR,ha⟩:=tiltedKernelPower_analytic_radius z hz hzr h
  apply scaledCenteredFourier_integrable
  exact ha.continuousOn.mono (by
    intro w hw
    have hn:‖w‖=1:=by simpa only[Metric.mem_sphere,dist_zero_right] using hw
    simpa only[Metric.mem_ball,dist_zero_right,hn] using hR)
lemma tiltedKernelMass_scaled_fourier_at_mean (z:ℝ)(hz:0<z)(hzr:z≤ r 0)(h m:ℕ)(hh:0<h)
    (hm:(m:ℝ)=(h:ℝ)*unscaledMean z):
    ((Real.sqrt ((h:ℝ)*tiltedKernelVariance z)*tiltedKernelMass z h m:ℝ):ℂ)=
      ((2*Real.pi:ℝ):ℂ)⁻¹*∫t:ℝ,scaledTiltedKernelFourier z h t:=by
  obtain ⟨R,hR,ha⟩:=tiltedKernelPower_analytic_radius z hz hzr h
  have hσ:0<Real.sqrt ((h:ℝ)*tiltedKernelVariance z):=Real.sqrt_pos.mpr
    (mul_pos (by exact_mod_cast hh) (tiltedKernelVariance_pos z hz hzr))
  have hi:=signedTaylorCoeff_scaled_fourier (fun w:ℂ=>(tiltedKernelPGF z w)^h) R hR
    ha.differentiableOn ((h:ℝ)*unscaledMean z) _ hσ (m:ℤ)
  simpa only[signedTaylorCoeff,Int.natCast_nonneg,ite_true,Int.toNat_natCast,
    tiltedKernelPower_coeff_complex,←Complex.ofReal_mul,Int.cast_natCast,hm,sub_self,
    zero_div,Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,one_mul,scaledTiltedKernelFourier] using hi
lemma scaledTiltedKernelFourier_gaussian_domination:
    ∃b:ℝ,0<b∧∀z:ℝ,0<z→z≤ r 0→∀h:ℕ,0<h→∀t:ℝ,
      ‖scaledTiltedKernelFourier z h t‖≤ Real.exp (-b*t^2):=by
  obtain ⟨c,hc,hbound⟩:=tiltedKernelPower_characteristic_bound
  obtain ⟨C,hC,hmean⟩:=unscaledMean_uniform_linear_variance_bounds
  refine ⟨c/C,div_pos hc hC,?_⟩
  intro z hz hzr h hh t
  have hhR:0<(h:ℝ):=by exact_mod_cast hh
  have hv:0<tiltedKernelVariance z:=tiltedKernelVariance_pos z hz hzr
  let σ:ℝ:=Real.sqrt ((h:ℝ)*tiltedKernelVariance z)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hhR hv)
  have hσsq:σ^2=(h:ℝ)*z*deriv unscaledMean z:=by
    rw[Real.sq_sqrt (mul_pos hhR hv).le]
    dsimp[tiltedKernelVariance]
    ring
  have hD:0<deriv unscaledMean z:=lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (hmean z ⟨hz.le,hzr⟩).2.2.1
  have hDC:deriv unscaledMean z≤ C:=(hmean z ⟨hz.le,hzr⟩).2.2.2
  change ‖scaledCenteredFourier _ _ σ t‖≤_
  rw[scaledCenteredFourier_norm]
  by_cases ht:t∈Icc (-(Real.pi*σ)) (Real.pi*σ)
  · rw[Set.indicator_of_mem ht]
    have hθ:|t/σ|≤ Real.pi:=by
      rw[abs_div,abs_of_pos hσ]
      exact (div_le_iff₀ hσ).mpr (by simpa only[mul_comm] using abs_le.mpr ht)
    have hb:=hbound z ⟨hz.le,hzr⟩ h (t/σ) hθ
    apply hb.trans
    apply Real.exp_le_exp.mpr
    have heq:-c*(h:ℝ)*z*(t/σ)^2=-(c/deriv unscaledMean z)*t^2:=by
      rw[div_pow,hσsq]
      field_simp
    rw[heq]
    have hquot:c/C≤ c/deriv unscaledMean z:=div_le_div_of_nonneg_left hc.le hD hDC
    nlinarith[mul_le_mul_of_nonneg_right hquot (sq_nonneg t)]
  · rw[Set.indicator_of_notMem ht]
    exact (Real.exp_pos _).le
end WP.Coefficients
