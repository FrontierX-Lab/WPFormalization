import WPFormalization.Analysis.AnalyticAverageContractions
import WPFormalization.Analysis.ParameterContraction

/-! Analytic division by a scalar coordinate, with genuine parameter germs.
The quotient is the integral of the actual coordinate derivative. Uniform
formal-series integration proves joint analyticity; the fundamental theorem
of calculus proves the factor identity. Two divisions give the square factor. -/
noncomputable section
set_option maxHeartbeats 300000
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def parameterDifferenceQuotient (F:E × ℂ → ℂ) (v:E × ℂ):ℂ:=
  ∫t:ℝ in (0)..1,fderiv ℂ F (parameterContraction t v) ((0,1):E × ℂ)
lemma parameterDifferenceQuotient_analyticAt (F:E × ℂ → ℂ) (hF:AnalyticAt ℂ F 0):
    AnalyticAt ℂ (parameterDifferenceQuotient F) 0:=by
  have hg:AnalyticAt ℂ (fun p:E × ℂ=>fderiv ℂ F p ((0,1):E × ℂ)) 0:=
    ((ContinuousLinearMap.apply ℂ ℂ ((0,1):E × ℂ)).analyticAt _).comp hF.fderiv
  exact analyticAt_interval_average_contractions _ hg _ parameterContraction_continuous parameterContraction_norm_le
lemma parameterDifferenceQuotient_identity (F:E × ℂ → ℂ) (hF:AnalyticAt ℂ F 0):
    ∀ᶠv:E × ℂ in 𝓝 0,F v-F (v.1,0)=v.2*parameterDifferenceQuotient F v:=by
  obtain ⟨r,hr,hball⟩:=Metric.eventually_nhds_iff.mp hF.eventually_analyticAt
  have hG(p:E × ℂ) (hp:‖p‖<r):
      AnalyticAt ℂ (fun q:E × ℂ=>fderiv ℂ F q ((0,1):E × ℂ)) p:=by
    exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1):E × ℂ)).analyticAt _).comp
      (hball (by simpa only[dist_zero_right] using hp)).fderiv
  filter_upwards[Metric.ball_mem_nhds (0:E × ℂ) hr] with v hv
  have hvr:‖v‖<r:=by simpa only[Metric.mem_ball,dist_zero_right] using hv
  have hAt(t:ℝ) (ht:t∈Icc (0:ℝ) 1):‖parameterContraction t v‖<r:=by
    have hm:max ‖v.1‖ ‖v.2‖<r:=by simpa only[Prod.norm_def] using hvr
    rw[parameterContraction_apply,Prod.norm_def,norm_mul,Complex.norm_of_nonneg ht.1]
    exact max_lt ((le_max_left _ _).trans_lt hm)
      ((mul_le_of_le_one_left (norm_nonneg v.2) ht.2).trans_lt ((le_max_right _ _).trans_lt hm))
  have hd(t:ℝ) (ht:t∈Icc (0:ℝ) 1):
      HasDerivAt (fun s:ℝ=>F (parameterContraction s v))
        (v.2*fderiv ℂ F (parameterContraction t v) ((0,1):E × ℂ)) t:=by
    have hfa:AnalyticAt ℂ F (parameterContraction t v):=
      hball (by simpa only[dist_zero_right] using hAt t ht)
    have hc:HasDerivAt (fun z:ℂ=>(v.1,z*v.2)) ((0,v.2):E × ℂ) (t:ℂ):=by
      simpa only[id_eq,one_mul] using
        (hasDerivAt_const (t:ℂ) v.1).prodMk ((hasDerivAt_id (t:ℂ)).mul_const v.2)
    have hfa':HasFDerivAt F (fderiv ℂ F (parameterContraction t v)) (v.1,(t:ℂ)*v.2):=by
      simpa only[parameterContraction_apply] using hfa.differentiableAt.hasFDerivAt
    have hh:=(hfa'.comp_hasDerivAt (t:ℂ) hc).comp_ofReal
    have he:(fderiv ℂ F (parameterContraction t v)) ((0,v.2):E × ℂ)=
        v.2*fderiv ℂ F (parameterContraction t v) ((0,1):E × ℂ):=by
      have hsm:=(fderiv ℂ F (parameterContraction t v)).map_smul v.2 ((0,1):E × ℂ)
      simpa only[Prod.smul_mk,smul_zero,smul_eq_mul,mul_one] using hsm
    rw[he] at hh
    simpa only[Function.comp_def,parameterContraction_apply] using hh
  have hcv:Continuous (fun t:ℝ=>parameterContraction t v):=
    (parameterContraction_continuous (E:=E)).clm_apply continuous_const
  have hgcont:ContinuousOn (fun t:ℝ=>fderiv ℂ F (parameterContraction t v) ((0,1):E × ℂ)) (Icc (0:ℝ) 1):=by
    intro t ht
    exact ((hG _ (hAt t ht)).continuousAt.comp
      (f:=fun s:ℝ=>parameterContraction s v) hcv.continuousAt).continuousWithinAt
  have hint:IntervalIntegrable (fun t:ℝ=>v.2*fderiv ℂ F (parameterContraction t v) ((0,1):E × ℂ)) volume 0 1:=by
    apply ContinuousOn.intervalIntegrable
    simpa only[uIcc_of_le (by norm_num : (0:ℝ)≤1),Pi.mul_def] using (continuousOn_const.mul hgcont)
  have hFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=1) (fun t ht=>hd t (by simpa only[uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht)) hint
  rw[intervalIntegral.integral_const_mul] at hFTC
  simpa only[parameterContraction_apply,Complex.ofReal_one,one_mul,Complex.ofReal_zero,zero_mul,
    Prod.mk.eta,parameterDifferenceQuotient] using hFTC.symm
end WP.Analysis
namespace WP.Analysis
open Filter
open scoped Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma parameterDifferenceQuotient_axis (F:E × ℂ → ℂ) (p:E):
    parameterDifferenceQuotient F (p,0)=fderiv ℂ F (p,0) ((0,1):E × ℂ):=by
  simp[parameterDifferenceQuotient,parameterContraction_apply]
lemma fderiv_axis_eq_deriv_slice (F:E × ℂ → ℂ) (p:E) (hF:AnalyticAt ℂ F (p,0)):
    fderiv ℂ F (p,0) ((0,1):E × ℂ)=deriv (fun u:ℂ=>F (p,u)) 0:=by
  have hc:HasDerivAt (fun u:ℂ=>(p,u)) ((0,1):E × ℂ) 0:=
    (hasDerivAt_const 0 p).prodMk (hasDerivAt_id 0)
  have hh:=hF.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hc
  simpa only[Function.comp_def] using hh.deriv.symm
lemma exists_analytic_parameter_factor (F:E × ℂ → ℂ) (hF:AnalyticAt ℂ F 0)
    (haxis:∀ᶠp:E in 𝓝 0,F (p,0)=0):
    ∃G:E × ℂ → ℂ,AnalyticAt ℂ G 0∧∀ᶠv:E × ℂ in 𝓝 0,F v=v.2*G v:=by
  refine ⟨parameterDifferenceQuotient F,parameterDifferenceQuotient_analyticAt F hF,?_⟩
  have ht:Tendsto (fun v:E × ℂ=>v.1) (𝓝 0) (𝓝 0):=continuous_fst.continuousAt.tendsto
  filter_upwards[parameterDifferenceQuotient_identity F hF,ht.eventually haxis] with v hv hzero
  simpa only[hzero,sub_zero] using hv
lemma exists_analytic_parameter_square_factor (F:E × ℂ → ℂ) (hF:AnalyticAt ℂ F 0)
    (haxis:∀ᶠp:E in 𝓝 0,F (p,0)=0)
    (hderiv:∀ᶠp:E in 𝓝 0,deriv (fun u:ℂ=>F (p,u)) 0=0):
    ∃G:E × ℂ → ℂ,AnalyticAt ℂ G 0∧∀ᶠv:E × ℂ in 𝓝 0,F v=v.2^2*G v:=by
  let H:E × ℂ → ℂ:=parameterDifferenceQuotient F
  have hH:AnalyticAt ℂ H 0:=parameterDifferenceQuotient_analyticAt F hF
  have ht:Tendsto (fun p:E=>(p,(0:ℂ))) (𝓝 0) (𝓝 (0:E × ℂ)):=
    continuous_id.continuousAt.prodMk continuous_const.continuousAt |>.tendsto
  have hHaxis:∀ᶠp:E in 𝓝 0,H (p,0)=0:=by
    filter_upwards[ht.eventually hF.eventually_analyticAt,hderiv] with p hp hd
    change parameterDifferenceQuotient F (p,0)=0
    rw[parameterDifferenceQuotient_axis,fderiv_axis_eq_deriv_slice F p hp,hd]
  obtain ⟨G,hG,hfactor⟩:=exists_analytic_parameter_factor H hH hHaxis
  refine ⟨G,hG,?_⟩
  have hfst:Tendsto (fun v:E × ℂ=>v.1) (𝓝 0) (𝓝 0):=continuous_fst.continuousAt.tendsto
  filter_upwards[parameterDifferenceQuotient_identity F hF,hfst.eventually haxis,hfactor] with v hv hzero hfac
  rw[hzero,sub_zero] at hv
  change H v=v.2*G v at hfac
  change F v=v.2^2*G v
  change F v=v.2*H v at hv
  rw[hv,hfac]
  ring
end WP.Analysis
namespace WP.Analysis
open Filter
open scoped Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma exists_analytic_parameter_square_factor_with_value (F:E × ℂ → ℂ) (hF:AnalyticAt ℂ F 0)
    (haxis:∀ᶠp:E in 𝓝 0,F (p,0)=0)
    (hderiv:∀ᶠp:E in 𝓝 0,deriv (fun u:ℂ=>F (p,u)) 0=0):
    ∃G:E × ℂ → ℂ,AnalyticAt ℂ G 0∧
      G 0=iteratedDeriv 2 (fun u:ℂ=>F (0,u)) 0/2 ∧
      ∀ᶠv:E × ℂ in 𝓝 0,F v=v.2^2*G v:=by
  obtain ⟨G,hG,hfac⟩:=exists_analytic_parameter_square_factor F hF haxis hderiv
  refine ⟨G,hG,?_,hfac⟩
  have ht:Tendsto (fun u:ℂ=>((0:E),u)) (𝓝 0) (𝓝 (0:E × ℂ)):=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt |>.tendsto
  have he:(fun u:ℂ=>F (0,u))=ᶠ[𝓝 0] (fun u:ℂ=>u^2*G (0,u)):=ht.eventually hfac
  have hs:AnalyticAt ℂ (fun u:ℂ=>G (0,u)) 0:=hG.comp (f:=fun u:ℂ=>((0:E),u)) (analyticAt_const.prod analyticAt_id)
  have hj:=he.iteratedDeriv_eq 2
  rw[iteratedDeriv_fun_mul (by fun_prop) hs.contDiffAt] at hj
  norm_num[Finset.sum_range_succ,iteratedDeriv_fun_pow_zero,iteratedDeriv_zero] at hj
  change G (0,0)=_
  linear_combination -hj/2
end WP.Analysis
