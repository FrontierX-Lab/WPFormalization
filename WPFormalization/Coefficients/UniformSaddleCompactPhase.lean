import WPFormalization.Coefficients.UniformSaddleMatching
import WPFormalization.Volumes.CompactLeadingChart
import WPFormalization.Analysis.RealAnalyticTrace
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: CompactPhase. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
open WP.Analysis
lemma unscaled_kernel_compact_phase_data (a:ℝ)(ha:0<a)(har:a≤ r 0):
    ∃(R:ℝ)(S L:ℂ→ℂ)(Ω:Set ℂ)(ρ:ℝ),r 0<R ∧ 0<ρ ∧ IsOpen Ω ∧
      AnalyticOnNhd ℂ S (Metric.ball 0 R) ∧
      (∀w∈Metric.ball (0:ℂ) R,HasDerivAt S (kernelLogSlope w) w) ∧
      (∀w∈Metric.ball (0:ℂ) R,Complex.exp (S w)=(H 0 w)⁻¹) ∧
      (∀z∈Icc a (r 0),(z:ℂ)∈Ω ∧ AnalyticAt ℂ S (z:ℂ) ∧ AnalyticAt ℂ L (z:ℂ) ∧
        S (z:ℂ)=((-Real.log (H 0 z).re:ℝ):ℂ) ∧
        complexEuler S (z:ℂ)=(unscaledMean z:ℂ) ∧
        ((complexEuler^[2]) S) (z:ℂ)=((z*deriv unscaledMean z:ℝ):ℂ) ∧
        L (z:ℂ)=((Real.sqrt (z*deriv unscaledMean z))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (z:ℂ),(L q)^2*((complexEuler^[2]) S) q=1) ∧
      ∀z∈Ω,∀u:ℂ,‖u‖<ρ→ AnalyticAt ℂ (centeredExponentialPhase S L) (z,u) ∧
        ‖centeredExponentialPhase S L (z,u)‖≤‖u‖^2:=by
  obtain ⟨R,S,hR,hSa,hS0,hSd0,hSd,hSr,hExp⟩:=unscaled_kernel_log_action
  have hRp:0<R:=ha.trans_le (har.trans hR.le)
  let v:ℂ→ℂ:=(complexEuler^[2]) S
  let L:ℂ→ℂ:=fun z=>(Complex.sqrt (v z))⁻¹
  have hdata:∀z∈Icc a (r 0),AnalyticAt ℂ S (z:ℂ) ∧ AnalyticAt ℂ L (z:ℂ) ∧
        S (z:ℂ)=((-Real.log (H 0 z).re:ℝ):ℂ) ∧
        complexEuler S (z:ℂ)=(unscaledMean z:ℂ) ∧
        v (z:ℂ)=((z*deriv unscaledMean z:ℝ):ℂ) ∧
        L (z:ℂ)=((Real.sqrt (z*deriv unscaledMean z))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (z:ℂ),(L q)^2*v q=1:=by
    intro z hz
    have hz0:0<z:=ha.trans_le hz.1
    have hzfull:z∈Icc (0:ℝ) (WP.r 0):=⟨hz0.le,hz.2⟩
    have hzR:(z:ℂ)∈Metric.ball (0:ℂ) R:=by
      rw[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz0]
      exact hz.2.trans_lt hR
    have hS:AnalyticAt ℂ S (z:ℂ):=hSa _ hzR
    have hE:complexEuler S =ᶠ[𝓝 (z:ℂ)] kernelComplexMean:=by
      filter_upwards[Metric.isOpen_ball.mem_nhds hzR] with w hw
      change w*deriv S w=w*kernelLogSlope w
      rw[(hSd w hw).deriv]
    have hν:complexEuler S (z:ℂ)=(unscaledMean z:ℂ):=hE.self_of_nhds.trans (kernelComplexMean_real z)
    have hκ:AnalyticAt ℂ kernelComplexMean (z:ℂ):=
      (complexEuler_analyticAt S (z:ℂ) hS).congr hE
    have htrace:(fun t:ℝ=>kernelComplexMean (t:ℂ))=ᶠ[𝓝 z] (fun t:ℝ=>(unscaledMean t:ℂ)):=
      .of_forall kernelComplexMean_real
    have hμ:AnalyticAt ℝ unscaledMean z:=analyticAt_real_of_complex_trace kernelComplexMean unscaledMean z hκ htrace
    have hvr:v (z:ℂ)=((z*deriv unscaledMean z:ℝ):ℂ):=by
      have ht:=iterated_complexEuler_real_trace kernelComplexMean unscaledMean z hκ hμ htrace 1
      simp only[Function.iterate_one,euler] at ht
      change (z:ℂ)*deriv (complexEuler S) (z:ℂ)=_
      rw[hE.deriv_eq]
      exact ht
    have hv:AnalyticAt ℂ v (z:ℂ):=
      complexEuler_analyticAt (complexEuler S) (z:ℂ) (complexEuler_analyticAt S (z:ℂ) hS)
    have hvp:0<z*deriv unscaledMean z:=mul_pos hz0
      (lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (unscaledMean_deriv_lower z hzfull))
    have hvne:v (z:ℂ)≠0:=by rw[hvr];exact_mod_cast hvp.ne'
    have hsqrt:AnalyticAt ℂ (fun w=>Complex.sqrt (v w)) (z:ℂ):=
      (complex_sqrt_analyticAt (by rw[hvr];exact Or.inl hvp)).comp (f:=v) hv
    have hsqreal:Complex.sqrt (v (z:ℂ))=(Real.sqrt (z*deriv unscaledMean z):ℂ):=by
      rw[hvr]
      exact Complex.sqrt_of_nonneg (by exact_mod_cast hvp.le)
    have hsqne:Complex.sqrt (v (z:ℂ))≠0:=by rw[hsqreal];exact_mod_cast (Real.sqrt_pos.mpr hvp).ne'
    have hL:AnalyticAt ℂ L (z:ℂ):=hsqrt.inv hsqne
    have hLr:L (z:ℂ)=((Real.sqrt (z*deriv unscaledMean z))⁻¹:ℝ):=by
      dsimp only[L]
      rw[hsqreal,Complex.ofReal_inv]
    refine ⟨hS,hL,hSr z hzfull,hν,hvr,hLr,?_⟩
    filter_upwards[hv.continuousAt.eventually_ne hvne] with q hq
    change (Complex.sqrt (v q))⁻¹^2*v q=1
    rw[inv_pow,complex_sqrt_sq,inv_mul_cancel₀ hq]
  let K:Set ℂ:=(fun z:ℝ=>(z:ℂ)) '' Icc a (r 0)
  have hK:IsCompact K:=isCompact_Icc.image Complex.continuous_ofReal
  have hF:∀z∈K,AnalyticAt ℂ (centeredExponentialPhase S L) (z,0):=by
    rintro z ⟨t,ht,rfl⟩
    exact centeredExponentialPhase_analyticAt S L (t:ℂ) (hdata t ht).1 (hdata t ht).2.1
  have hj:∀z∈K,∀ᶠq:ℂ in 𝓝 z,centeredExponentialPhase S L (q,0)=0 ∧
      deriv (fun u:ℂ=>centeredExponentialPhase S L (q,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>centeredExponentialPhase S L (q,u)) 0=-1:=by
    rintro z ⟨t,ht,rfl⟩
    obtain ⟨hSt,hLt,htrace,hν,hv,hLr,hunit⟩:=hdata t ht
    filter_upwards[hSt.eventually_analyticAt,hunit] with q hq hu
    exact ⟨by simp[centeredExponentialPhase,centeredExponentialSlice],
      (centeredExponentialSlice_jets S q (Complex.I*L q) hq).2.1,
      centeredExponentialPhase_second S L q hq hu⟩
  obtain ⟨Ω,hΩ,hKΩ,ρ,hρ,hprop⟩:=compact_normalized_phase_quadratic_bound K hK
    (centeredExponentialPhase S L) hF hj
  refine ⟨R,S,L,Ω,ρ,hR,hρ,hΩ,hSa,hSd,hExp,?_,hprop⟩
  intro z hz
  exact ⟨hKΩ ⟨z,hz,rfl⟩,hdata z hz⟩
end WP.Coefficients
