import WPFormalization.Coefficients.UniformSaddleProbability
import WPFormalization.Coefficients.UniformSaddleMatching
import WPFormalization.HigherOrder.PoissonPhaseChangeProof
import WPFormalization.HigherOrder.PoissonCentralScaling
import WPFormalization.HigherOrder.PoissonFamilyCoefficients
import WPFormalization.Analysis.PoissonPhasePrefactor
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Origin. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
open WP.HigherOrder
lemma tiltedKernelMass_poisson_phase_exact
    (S:ℂ→ℂ)(h:ℕ)(m:ℕ)(hh:0<h)(z:ℝ)(hz:0<z)(hzr:z≤ r 0)
    (xco Q:ℂ→ℂ)(f:ℂ × ℂ →ℂ)
    (hsource: (fun w:ℂ=>Complex.exp ((h:ℂ)*S w)) =ᶠ[𝓝 0]
      (fun w:ℂ=>(H 0 w)⁻¹^h))
    (hS:S (xco ((((m:ℝ)/(h:ℝ)):ℝ):ℂ))=((-Real.log (H 0 z).re:ℝ):ℂ))
    (hQ:Q ((((m:ℝ)/(h:ℝ)):ℝ):ℂ)=(((((m:ℝ)/(h:ℝ))/z:ℝ)):ℂ))
    (hcoeff:let ν:ℂ:=(m:ℂ)/(h:ℂ);
      WP.coeff (fun w:ℂ=>Complex.exp ((h:ℂ)*S w)) m =
        Complex.exp ((h:ℂ)*(S (xco ν)-ν+ν*Complex.log (Q ν)))*
          WP.coeff (fun u:ℂ=>Complex.exp ((h:ℂ)*u)*f (u,ν)) m):
    (tiltedKernelMass z h m:ℂ)=(poissonCenter m:ℂ)*
      poissonCoefficientOperator h m (fun u=>f (u,((((m:ℝ)/(h:ℝ)):ℝ):ℂ))):=by
  have hhR:0<(h:ℝ):=by exact_mod_cast hh
  have hhC:(h:ℂ)≠0:=by exact_mod_cast hh.ne'
  have hfac:(m.factorial:ℂ)≠0:=by exact_mod_cast m.factorial_ne_zero
  have hp:=Analysis.poisson_phase_prefactor_complex (h:ℝ) z (-Real.log (H 0 z).re) m hhR hz
    (S (xco ((((m:ℝ)/(h:ℝ)):ℝ):ℂ))) (Q ((((m:ℝ)/(h:ℝ)):ℝ):ℂ)) hS hQ
  have hc: (unscaledCoeff h m:ℂ)=
      ((Real.exp ((h:ℝ)*(-Real.log (H 0 z).re))*z⁻¹^m*poissonCenter m:ℝ):ℂ)*
        poissonCoefficientOperator h m (fun u=>f (u,((((m:ℝ)/(h:ℝ)):ℝ):ℂ))):=by
    rw[←unscaledCoeff_complex,←Analysis.coeff_congr_of_eventuallyEq _ _ hsource m]
    rw[hcoeff]
    rw[←hp]
    simp only[poissonCoefficientOperator,Complex.ofReal_natCast,Complex.ofReal_div]
    field_simp
  have hH:0<(H 0 z).re:=H_zero_re_pos z ⟨hz.le,hzr⟩
  have hexp:Real.exp ((h:ℝ)*(-Real.log (H 0 z).re))=((H 0 z).re)⁻¹^h:=by
    rw[mul_neg,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hH,inv_pow]
  rw[tiltedKernelMass_eq_unscaled,Complex.ofReal_mul,Complex.ofReal_mul,hc,hexp]
  have hzC:(z:ℂ)≠0:=by exact_mod_cast hz.ne'
  have hHC:((H 0 z).re:ℂ)≠0:=by exact_mod_cast hH.ne'
  simp only[Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv]
  simp only[inv_pow]
  field_simp [hHC,hzC]
end WP.Coefficients
namespace WP.Coefficients
open Set Filter
open scoped Topology
open WP.HigherOrder
lemma poisson_operator_origin_lower (f:ℂ × ℂ→ℂ)(hf:AnalyticAt ℂ f 0)(hf0:f 0=1):
    ∃ν₀ T:ℝ,0<ν₀∧0<T∧∀h:ℝ,∀m:ℕ,T≤ h→(m:ℝ)/h≤ν₀→
      1/2≤(poissonCoefficientOperator h m (fun u=>f (u,((((m:ℝ)/h):ℝ):ℂ)))).re:=by
  have he:∀ᶠv:ℂ × ℂ in 𝓝 0,AnalyticAt ℂ f v ∧ ‖f v-1‖<1/4:=by
    have hn:ContinuousAt (fun v=>‖f v-1‖) 0:=by fun_prop
    have hn0:‖f 0-1‖<(1/4:ℝ):=by rw[hf0];norm_num
    exact hf.eventually_analyticAt.and (hn.tendsto.eventually (eventually_lt_nhds hn0))
  obtain ⟨R,hR,hball⟩:=Metric.eventually_nhds_iff.mp he
  have ha:AnalyticOnNhd ℂ f (Metric.ball 0 R):=fun v hv=>(hball (by simpa only[Metric.mem_ball,dist_zero_right] using hv)).1
  have hb:∀v∈Metric.ball (0:ℂ × ℂ) R,‖f v‖≤2:=by
    intro v hv
    have hv':dist v 0<R:=hv
    have hn:‖f v-1‖<1/4:=(hball hv').2
    have ht:=norm_add_le (f v-1) (1:ℂ)
    simp only[sub_add_cancel,norm_one] at ht
    linarith
  obtain ⟨ν₀,C,hν,hνR,hC,hall⟩:=poisson_central_expansion_uniform_homogeneous R hR
  refine ⟨ν₀,max 1 (8*C),hν,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro h m hh hm
  have hh1:1≤ h:=(le_max_left _ _).trans hh
  have hh0:0<h:=zero_lt_one.trans_le hh1
  have hhC:8*C≤ h:=(le_max_right _ _).trans hh
  have herr:‖poissonCoefficientOperator h m (fun u=>f (u,((((m:ℝ)/h):ℝ):ℂ)))-
      f (((m:ℝ)/h:ℝ),((m:ℝ)/h:ℝ))‖≤2*C/h:=by
    have ht:=(hall f 2 (by norm_num) ha hb).1 h m 0 hh0 hm (by simpa only[Nat.cast_zero] using (half_pos hh0).le)
    simpa only[Finset.sum_range_one,poissonCentralAmplitude,ite_true,pow_zero,div_one,
      Nat.zero_add,pow_one,Nat.factorial_one,Nat.cast_one,mul_one] using ht
  have hn:‖((((m:ℝ)/h:ℝ):ℂ),(((m:ℝ)/h:ℝ):ℂ))‖<R:=by
    simp only[Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Nat.cast_nonneg m) hh0.le),max_self]
    exact hm.trans_lt hνR
  have hpoint:‖f ((((m:ℝ)/h:ℝ):ℂ),(((m:ℝ)/h:ℝ):ℂ))-1‖<1/4:=
    (hball (by simpa only[dist_zero_right] using hn)).2
  have hp:3/4≤(f ((((m:ℝ)/h:ℝ):ℂ),(((m:ℝ)/h:ℝ):ℂ))).re:=by
    have ht:=Complex.re_le_norm (1-f ((((m:ℝ)/h:ℝ):ℂ),(((m:ℝ)/h:ℝ):ℂ)))
    rw[norm_sub_rev] at ht
    simp only[Complex.sub_re,Complex.one_re] at ht
    linarith
  have her: (f ((((m:ℝ)/h:ℝ):ℂ),(((m:ℝ)/h:ℝ):ℂ))).re-
      (poissonCoefficientOperator h m (fun u=>f (u,((((m:ℝ)/h):ℝ):ℂ)))).re≤2*C/h:=by
    have ht:=Complex.re_le_norm (f ((((m:ℝ)/h:ℝ):ℂ),(((m:ℝ)/h:ℝ):ℂ))-
      poissonCoefficientOperator h m (fun u=>f (u,((((m:ℝ)/h):ℝ):ℂ))))
    rw[norm_sub_rev] at ht
    simpa only[Complex.sub_re] using ht.trans herr
  have hq:2*C/h≤1/4:=(div_le_iff₀ hh0).mpr (by nlinarith)
  linarith
end WP.Coefficients
namespace WP.Coefficients
open Set Filter
open scoped Topology
open WP.HigherOrder
lemma tiltedKernelMass_origin_lower :
    ∃ν₀ T:ℝ,0<ν₀∧0<T∧∀h m:ℕ,1≤ h→T≤(h:ℝ)→0 < m → (m:ℝ)/h≤ν₀→
      poissonCenter m/2≤ tiltedKernelMass (saddleZeta ((m:ℝ)/h)) h m:=by
  obtain ⟨R,S,hR,hSa,hS0,hSd0,hSd,hSr,hExp⟩:=unscaled_kernel_log_action
  have hRp:0<R:=(r_pos 0 ⟨le_rfl,y₀_pos⟩).trans hR
  have hSa0:=hSa 0 (Metric.mem_ball_self hRp)
  have hspos:0<(deriv S 0).re:=by rw[hSd0];norm_num
  obtain ⟨r₁,hr₁,xco,Q,Z,hx,hQ,hZ,hx0,hxd,hQ0,haxes,hphase,hamp⟩:=
    analytic_phase_change_complex_proof S hSa0 hspos
  obtain ⟨δ,hδ,hfa,hcoef⟩:=hamp (fun _=>1) analyticAt_const
  let f:ℂ × ℂ→ℂ:=phaseAmplitude Z (fun _=>1)
  have hf:AnalyticAt ℂ f 0:=hfa 0 ⟨Metric.mem_ball_self hδ,Metric.mem_ball_self hδ⟩
  have hZ0:Z 0=0:=by simpa only[Prod.zero_eq_mk] using (haxes 0 (by simpa only[norm_zero] using hr₁)).2.2.1
  have hq:phaseQuotient Z 0 0≠0:=(hphase 0 0 (by simpa only[norm_zero] using hr₁) (by simpa only[norm_zero] using hr₁)).1
  have hf0:f 0=1:=Analysis.phaseAmplitude_at_origin Z _ hZ0 hq
  obtain ⟨ν₁,T,hν₁,hT,hlower⟩:=poisson_operator_origin_lower f hf hf0
  have hsaddle:∀ᶠν:ℂ in 𝓝 0,xco ν*deriv S (xco ν)=ν:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hr₁] with ν hν
    exact (haxes ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).1
  have hmatch:=analytic_saddle_matches_saddleZeta R hRp S xco hSd
    (hx 0 (Metric.mem_ball_self hr₁)) hx0 hsaddle
  obtain ⟨η,hη,hmatching⟩:=Metric.mem_nhdsWithin_iff.mp hmatch
  let ν₀:ℝ:=min ν₁ (min (δ/2) (min (r₁/2) (min (η/2) 1)))
  have hν₀:0<ν₀:=lt_min hν₁ (lt_min (half_pos hδ) (lt_min (half_pos hr₁) (lt_min (half_pos hη) zero_lt_one)))
  refine ⟨ν₀,T,hν₀,hT,?_⟩
  intro h m hh hhT hm hmν
  let ν:ℝ:=(m:ℝ)/h
  let z:ℝ:=saddleZeta ν
  have hh0:0<h:=by omega
  have hhR:0<(h:ℝ):=by exact_mod_cast hh0
  have hhC:(h:ℂ)≠0:=by exact_mod_cast hh0.ne'
  have hν:0<ν:=div_pos (by exact_mod_cast hm) hhR
  have hν1:ν≤ν₁:=hmν.trans (min_le_left _ _)
  have hνδ:ν<δ:=by
    have he:ν≤δ/2:=hmν.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hνr:ν<r₁:=by
    have he:ν≤ r₁/2:=hmν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hνη:ν<η:=by
    have he:ν≤η/2:=hmν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    linarith
  have hνU:ν≤3/2:=by
    have he:ν≤1:=hmν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    linarith
  have hz:0<z:=saddleZeta_pos ν hν hνU
  have hzr:z≤ r 0:=(saddleZeta_spec ν ⟨hν.le,hνU⟩).1.2
  have hxe:xco (ν:ℂ)=(z:ℂ):=hmatching ⟨by simpa only[Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hν] using hνη,hν.le⟩
  have hnν:‖(ν:ℂ)‖<r₁:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos hν] using hνr
  have hphaseQ:Q (ν:ℂ)=((ν/z:ℝ):ℂ):=by
    rw[(haxes _ hnν).2.1 (by exact_mod_cast hν.ne'),hxe]
    exact (Complex.ofReal_div ν z).symm
  have hphaseS:S (xco (ν:ℂ))=((-Real.log (H 0 z).re:ℝ):ℂ):=by
    rw[hxe]
    exact hSr z ⟨hz.le,hzr⟩
  have hsource:(fun w:ℂ=>Complex.exp ((h:ℂ)*S w)) =ᶠ[𝓝 0] (fun w:ℂ=>(H 0 w)⁻¹^h):=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hRp] with w hw
    rw[Complex.exp_nat_mul,hExp w hw]
  have hcoef':let ν:ℂ:=(m:ℂ)/(h:ℂ);
      WP.coeff (fun w:ℂ=>Complex.exp ((h:ℂ)*S w)) m =
        Complex.exp ((h:ℂ)*(S (xco ν)-ν+ν*Complex.log (Q ν)))*
          WP.coeff (fun u:ℂ=>Complex.exp ((h:ℂ)*u)*f (u,ν)) m:=by
    have hc:=hcoef (h:ℂ) m hhC (by simpa only[norm_div,Complex.norm_natCast] using hνδ)
    simpa only[mul_one] using hc
  have he:=tiltedKernelMass_poisson_phase_exact S h m hh0 z hz hzr xco Q f hsource hphaseS hphaseQ hcoef'
  have heR:tiltedKernelMass z h m=poissonCenter m*
      (poissonCoefficientOperator h m (fun u=>f (u,(ν:ℂ)))).re:=by
    simpa only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using congrArg Complex.re he
  have hp:0≤ poissonCenter m:=by unfold poissonCenter;positivity
  rw[heR]
  have hlo:=hlower h m hhT hν1
  nlinarith
end WP.Coefficients
