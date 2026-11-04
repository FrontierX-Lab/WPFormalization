import WPFormalization.Coefficients.UniformSaddleBasic
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Mean. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma r_zero_value : r 0=Real.pi^2/2:=by
  have he:=(stationary_root_proof 0 ⟨le_rfl,y₀_pos⟩).2.2.2
  rw[Delta,T_zero_value,sub_zero] at he
  linarith
lemma H_zero_re_pos (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0)):0<(H 0 z).re:=
  Analysis.H_re_pos_to_r 0 ⟨le_rfl,y₀_pos⟩ z hz
lemma unscaledMean_at_r : unscaledMean (r 0)=3/2:=by
  have hd:=kernel_differential 0 (r 0:ℂ)
  have hk:K 0 (r 0:ℂ)=0:=by simpa only[Complex.ofReal_zero] using Analysis.K_r_zero 0 ⟨le_rfl,y₀_pos⟩
  rw[hk] at hd
  have hr:=congrArg Complex.re hd
  norm_num[Complex.mul_re,Complex.mul_im] at hr
  unfold unscaledMean
  apply (div_eq_iff (H_zero_re_pos _ ⟨(r_pos 0 ⟨le_rfl,y₀_pos⟩).le,le_rfl⟩).ne').mpr
  nlinarith
lemma unscaled_kernel_zero_free_radius:
    ∃R:ℝ,r 0<R∧∀w:ℂ,‖w‖≤ R→H 0 w≠0:=by
  obtain ⟨ε,hε,hzero⟩:=Analysis.barH_uniform_zero_free
  have hr:0<r 0:=r_pos 0 ⟨le_rfl,y₀_pos⟩
  let R:ℝ:=r 0*(1+ε)
  have hR:r 0<R:=by dsimp[R];nlinarith
  refine ⟨R,hR,?_⟩
  intro w hw
  let v:ℂ:=w/(r 0:ℂ)
  have hv:‖v‖≤1+ε:=by
    rw[norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by simpa only[R,mul_comm] using hw)
  have he:barH 0 v=H 0 w:=by
    simp only[barH,ite_eq_right (ne_of_lt y₀_pos),Complex.ofReal_zero,a_zero,Complex.ofReal_one,div_one]
    congr 1
    dsimp[v]
    have hrC:(r 0:ℂ)≠0:=by exact_mod_cast hr.ne'
    field_simp[hrC]
  have hn:=hzero 0 ⟨le_rfl,y₀_pos.le⟩ v hv
  rwa[he] at hn

def kernelLogSlope (w:ℂ):ℂ:=-deriv (H 0) w/H 0 w
def kernelComplexMean (w:ℂ):ℂ:=w*kernelLogSlope w
lemma kernelComplexMean_re (z:ℝ):(kernelComplexMean (z:ℂ)).re=unscaledMean z:=by
  unfold kernelComplexMean kernelLogSlope unscaledMean
  rw[H_zero_real z]
  simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,mul_zero,zero_mul,sub_zero,Complex.div_ofReal_re]
  ring
lemma kernelLogSlope_zero : kernelLogSlope 0=1/5:=by
  have hd:deriv (H 0) 0=(-1/5:ℂ):=by
    have he:=Analysis.coeff_H_zero_eq_bessel 1
    rw[Analysis.normalizedBesselCoeff_five_two] at he
    norm_num[WP.coeff,oddFactorial,Finset.prod_range_succ] at he
    simpa only[neg_div] using he
  simp only[kernelLogSlope,H_zero,Analysis.derivX_zero,hd,neg_div,neg_neg,div_one]
lemma kernelLogSlope_coeff_pos (n:ℕ):0<realCoeff kernelLogSlope n:=
  Analysis.H_logarithmic_coeff_pos 0 ⟨le_rfl,y₀_pos⟩ n
end WP.Coefficients
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma kernelLogSlope_analyticAt (R:ℝ)(hzero:∀w:ℂ,‖w‖<R→H 0 w≠0)
    (z:ℂ)(hz:‖z‖<R):AnalyticAt ℂ kernelLogSlope z:=
  (((H_differentiable 0).analyticAt z).deriv.neg).div ((H_differentiable 0).analyticAt z) (hzero z hz)
lemma kernelComplexMean_analyticAt (R:ℝ)(hzero:∀w:ℂ,‖w‖<R→H 0 w≠0)
    (z:ℂ)(hz:‖z‖<R):AnalyticAt ℂ kernelComplexMean z:=
  analyticAt_id.mul (kernelLogSlope_analyticAt R hzero z hz)
lemma meanDerivativeCoeff_pos (n:ℕ):0<realCoeff (deriv kernelComplexMean) n:=by
  have hL:AnalyticAt ℂ kernelLogSlope 0:=by
    exact (((H_differentiable 0).analyticAt 0).deriv.neg).div ((H_differentiable 0).analyticAt 0)
      (by rw[H_zero,Analysis.derivX_zero];norm_num)
  have he:=congrArg (PowerSeries.coeff n) (Analysis.taylor_deriv (f:=kernelComplexMean))
  simp only[Analysis.taylor_coeff,PowerSeries.coeff_derivative] at he
  have hc:WP.coeff kernelComplexMean (n+1)=WP.coeff kernelLogSlope n:=by
    change WP.coeff (fun w:ℂ=>w*kernelLogSlope w) (n+1)=_
    have hh:=Analysis.coeff_id_pow_mul kernelLogSlope hL 1 (n+1)
    simpa only[pow_one,Nat.le_add_left,ite_true,Nat.add_sub_cancel] using hh
  unfold realCoeff
  rw[he,hc,Complex.mul_re]
  simp only[Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.add_im,Complex.natCast_im,
    Complex.one_im,zero_add,zero_mul,mul_zero,sub_zero]
  exact mul_pos (kernelLogSlope_coeff_pos n) (by positivity:(0:ℝ)<(n:ℝ)+1)
lemma kernelComplexMean_deriv_zero : deriv kernelComplexMean 0=1/5:=by
  have hL:AnalyticAt ℂ kernelLogSlope 0:=
    (((H_differentiable 0).analyticAt 0).deriv.neg).div ((H_differentiable 0).analyticAt 0)
      (by rw[H_zero,Analysis.derivX_zero];norm_num)
  have hd:=(hasDerivAt_id (0:ℂ)).mul hL.differentiableAt.hasDerivAt
  change deriv (fun i:ℂ=>i*kernelLogSlope i) 0=1/5
  simpa only[Pi.mul_def,id_eq,mul_one,one_mul,zero_mul,add_zero,kernelLogSlope_zero] using hd.deriv
lemma unscaledMean_hasDerivAt (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0)):
    HasDerivAt unscaledMean (deriv kernelComplexMean (z:ℂ)).re z:=by
  obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
  have hzn:‖(z:ℂ)‖<R:=by rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1];exact hz.2.trans_lt hR
  have ha:=kernelComplexMean_analyticAt R (fun w hw=>hzero w hw.le) (z:ℂ) hzn
  have hc:=Complex.reCLM.hasFDerivAt.comp_hasDerivAt z ha.differentiableAt.hasDerivAt.comp_ofReal
  simpa only[Function.comp_def,Complex.reCLM_apply,kernelComplexMean_re] using hc
lemma unscaledMean_deriv_lower (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0)):
    1/5≤ deriv unscaledMean z:=by
  obtain ⟨R,hR,hzero⟩:=unscaled_kernel_zero_free_radius
  have hzn:‖(z:ℂ)‖<R:=by rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1];exact hz.2.trans_lt hR
  have hdiff:DifferentiableOn ℂ (deriv kernelComplexMean) (Metric.ball 0 R):=by
    intro w hw
    exact (kernelComplexMean_analyticAt R (fun w hw=>hzero w hw.le) w
      (by simpa only[Metric.mem_ball,dist_zero_right] using hw)).deriv.differentiableAt.differentiableWithinAt
  have hs:=Analysis.hasSum_coeff_on_ball (deriv kernelComplexMean) R hdiff (z:ℂ) hzn
  have hsR:HasSum (fun n:ℕ=>realCoeff (deriv kernelComplexMean) n*z^n) (deriv kernelComplexMean (z:ℂ)).re:=by
    convert Complex.hasSum_re hs using 1
    ext n
    simp only[←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]
  have hlo:=hsR.summable.le_tsum 0 (fun n _=>mul_nonneg (meanDerivativeCoeff_pos n).le (pow_nonneg hz.1 _))
  rw[hsR.tsum_eq,pow_zero,mul_one] at hlo
  have hfirst:realCoeff (deriv kernelComplexMean) 0=1/5:=by
    simp only[realCoeff,WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,kernelComplexMean_deriv_zero]
    norm_num
  rw[hfirst] at hlo
  rw[(unscaledMean_hasDerivAt z hz).deriv]
  exact hlo
lemma unscaledMean_strictMonoOn:StrictMonoOn unscaledMean (Icc (0:ℝ) (r 0)):=by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro z hz
    exact (unscaledMean_hasDerivAt z hz).continuousAt.continuousWithinAt
  · intro z hz
    exact lt_of_lt_of_le (by norm_num:0<(1/5:ℝ)) (unscaledMean_deriv_lower z (interior_subset hz))
end WP.Coefficients
namespace WP.Coefficients
open Set
lemma saddleZeta_spec (u:ℝ)(hu:u∈Icc (0:ℝ) (3/2)):
    saddleZeta u∈Icc (0:ℝ) (r 0)∧unscaledMean (saddleZeta u)=u:=by
  have hr:0<r 0:=r_pos 0 ⟨le_rfl,y₀_pos⟩
  have hcont:ContinuousOn unscaledMean (Icc (0:ℝ) (r 0)):=
    fun z hz=>(unscaledMean_hasDerivAt z hz).continuousAt.continuousWithinAt
  have himage:=intermediate_value_Icc hr.le hcont
  have hu':u∈Icc (unscaledMean 0) (unscaledMean (r 0)):=by
    rw[unscaledMean_zero,unscaledMean_at_r]
    exact hu
  obtain ⟨z,hz,he⟩:=himage hu'
  have hset:{x:ℝ|x∈Icc (0:ℝ) (Real.pi^2/2)∧unscaledMean x=u}={z}:=by
    ext x
    constructor
    · intro hx
      have hx':x∈Icc (0:ℝ) (r 0):=by simpa only[r_zero_value] using hx.1
      exact mem_singleton_iff.mpr (unscaledMean_strictMonoOn.injOn hx' hz (hx.2.trans he.symm))
    · intro hx
      have hxe:x=z:=mem_singleton_iff.mp hx
      subst x
      exact ⟨by simpa only[r_zero_value] using hz,he⟩
  have hζ:saddleZeta u=z:=by unfold saddleZeta;rw[hset,csInf_singleton]
  rw[hζ]
  exact ⟨hz,he⟩
lemma saddleZeta_pos (u:ℝ)(hu:0<u)(huU:u≤3/2):0<saddleZeta u:=by
  have hs:=saddleZeta_spec u ⟨hu.le,huU⟩
  by_contra hh
  have he:saddleZeta u=0:=le_antisymm (le_of_not_gt hh) hs.1.1
  rw[he,unscaledMean_zero] at hs
  linarith[hs.2]
end WP.Coefficients
