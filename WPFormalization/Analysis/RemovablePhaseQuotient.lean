import WPFormalization.Analysis.PoissonPhaseAmplitude
import WPFormalization.Analysis.ParameterHadamard
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma parameterDifferenceQuotient_removable_germ (Y:ℂ × ℂ → ℂ) (hY:AnalyticAt ℂ Y 0)
    (haxis:∀ᶠν:ℂ in 𝓝 0,Y (ν,0)=0):
    ∀ᶠv:ℂ × ℂ in 𝓝 0,parameterDifferenceQuotient Y v=
      if v.2=0 then deriv (fun u:ℂ=>Y (v.1,u)) 0 else Y v/v.2:=by
  have ht:Tendsto (fun v:ℂ × ℂ=>v.1) (𝓝 0) (𝓝 0):=continuous_fst.continuousAt.tendsto
  have ht0:Tendsto (fun ν:ℂ=>(ν,(0:ℂ))) (𝓝 0) (𝓝 (0:ℂ × ℂ)):=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  filter_upwards[parameterDifferenceQuotient_identity Y hY,ht.eventually haxis,
    ht.eventually (ht0.eventually hY.eventually_analyticAt)] with v hf ha hya
  rw[ha,sub_zero] at hf
  by_cases hz:v.2=0
  · rw[if_pos hz]
    have hv:v=(v.1,0):=Prod.ext rfl hz
    rw[hv,parameterDifferenceQuotient_axis,fderiv_axis_eq_deriv_slice Y v.1 hya]
  · rw[if_neg hz,hf]
    simpa only[mul_comm] using (mul_div_cancel_right₀ (parameterDifferenceQuotient Y v) hz).symm
lemma phaseQuotient_analyticAt_zero_of_axis (Z:ℂ × ℂ → ℂ) (hZ:AnalyticAt ℂ Z 0)
    (haxis:∀ᶠν:ℂ in 𝓝 0,Z (0,ν)=0):
    AnalyticAt ℂ (fun v:ℂ × ℂ=>phaseQuotient Z v.1 v.2) 0:=by
  let sw:ℂ × ℂ → ℂ × ℂ:=fun v=>(v.2,v.1)
  have hsw:AnalyticAt ℂ sw 0:=analyticAt_snd.prod analyticAt_fst
  have hsw0:sw 0=0:=by rfl
  let Y:ℂ × ℂ → ℂ:=fun v=>Z (sw v)
  have hY:AnalyticAt ℂ Y 0:=by
    have hh:AnalyticAt ℂ Z (sw 0):=by rw[hsw0];exact hZ
    exact hh.comp (f:=sw) hsw
  have hq:AnalyticAt ℂ (fun v:ℂ × ℂ=>parameterDifferenceQuotient Y (sw v)) 0:=by
    have hh:AnalyticAt ℂ (parameterDifferenceQuotient Y) (sw 0):=by
      rw[hsw0];exact parameterDifferenceQuotient_analyticAt Y hY
    exact hh.comp (f:=sw) hsw
  have ht:Tendsto sw (𝓝 0) (𝓝 0):=by simpa only[hsw0] using hsw.continuousAt.tendsto
  apply hq.congr
  filter_upwards[ht.eventually (parameterDifferenceQuotient_removable_germ Y hY haxis)] with v hv
  exact hv
lemma phaseAmplitude_one_analyticAt_zero_of_axis (Z:ℂ × ℂ → ℂ) (hZ:AnalyticAt ℂ Z 0)
    (haxis:∀ᶠν:ℂ in 𝓝 0,Z (0,ν)=0) (hq0:phaseQuotient Z 0 0≠0):
    AnalyticAt ℂ (phaseAmplitude Z (fun _:ℂ=>1)) 0:=by
  have hZ0:Z 0=0:=haxis.self_of_nhds
  exact phaseAmplitude_analyticAt_zero Z (fun v:ℂ × ℂ=>phaseQuotient Z v.1 v.2) hZ hZ0
    (phaseQuotient_analyticAt_zero_of_axis Z hZ haxis) hq0 (Filter.Eventually.of_forall (fun _=>rfl))
    (fun _:ℂ=>1) analyticAt_const
end WP.Analysis
