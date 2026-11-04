import WPFormalization.Analysis.AnalyticImplicitScalar
import WPFormalization.Analysis.ParameterCancellation
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma exists_poisson_phase_inverse (C:ℂ × ℂ → ℂ) (x:ℂ → ℂ)
    (hC:AnalyticAt ℂ C 0) (hCne:C 0≠0) (hx:AnalyticAt ℂ x 0) (hx0:x 0=0)
    (hsaddle:∀ᶠν:ℂ in 𝓝 0,x ν*C (x ν,ν)=ν):
    ∃Y:ℂ × ℂ → ℂ,AnalyticAt ℂ Y 0∧Y 0=0∧
      (∀ᶠv:ℂ × ℂ in 𝓝 0,Y v*C (Y v,v.1)=v.2)∧
      (∀ᶠν:ℂ in 𝓝 0,Y (ν,0)=0∧Y (ν,ν)=x ν):=by
  let F:((ℂ × ℂ) × ℂ) → ℂ:=fun p=>p.2*C (p.2,p.1.1)-p.1.2
  have hp1:AnalyticAt ℂ (fun p:(ℂ × ℂ) × ℂ=>p.1.1) 0:=
    (analyticAt_fst (𝕜:=ℂ) (p:=(0:ℂ × ℂ))).comp (f:=fun p:(ℂ × ℂ) × ℂ=>p.1) analyticAt_fst
  have hp2:AnalyticAt ℂ (fun p:(ℂ × ℂ) × ℂ=>p.1.2) 0:=
    (analyticAt_snd (𝕜:=ℂ) (p:=(0:ℂ × ℂ))).comp (f:=fun p:(ℂ × ℂ) × ℂ=>p.1) analyticAt_fst
  have hcp:AnalyticAt ℂ (fun p:(ℂ × ℂ) × ℂ=>C (p.2,p.1.1)) 0:=
    hC.comp (f:=fun p:(ℂ × ℂ) × ℂ=>(p.2,p.1.1)) (analyticAt_snd.prod hp1)
  have hF:AnalyticAt ℂ F 0:=(analyticAt_snd.mul hcp).sub hp2
  have hc0:HasDerivAt (fun z:ℂ=>C (z,0)) (deriv (fun z:ℂ=>C (z,0)) 0) 0:=
    (hC.comp (f:=fun z:ℂ=>(z,0)) (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
  have hd:HasDerivAt (fun z:ℂ=>F ((0:ℂ × ℂ),z)) (C 0) 0:=by
    convert! (hasDerivAt_id (0:ℂ)).mul hc0 using 1 <;>
      simp [F,Pi.mul_def] <;> rfl
  have hc:HasDerivAt (fun y:ℂ=>((0:ℂ × ℂ),y)) ((0,1):(ℂ × ℂ) × ℂ) 0:=
    (hasDerivAt_const 0 (0:ℂ × ℂ)).prodMk (hasDerivAt_id 0)
  have hh:HasDerivAt (fun y:ℂ=>F ((0:ℂ × ℂ),y))
      (fderiv ℂ F 0 ((0,1):(ℂ × ℂ) × ℂ)) 0:=by
    simpa only[Function.comp_def] using hF.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hc
  have he:fderiv ℂ F 0 ((0,1):(ℂ × ℂ) × ℂ)=C 0:=hh.unique hd
  have hInv:(fderiv ℂ F 0 ∘L ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).IsInvertible:=by
    apply complex_clm_isInvertible_of_apply_one_ne_zero
    change fderiv ℂ F 0 ((0,1):(ℂ × ℂ) × ℂ)≠0
    rw[he]
    exact hCne
  obtain ⟨Y,hY,hY0,hYE,huniq,hder⟩:=exists_analytic_implicit_scalar F 0 hF hInv
  have hYE':∀ᶠv:ℂ × ℂ in 𝓝 0,Y v*C (Y v,v.1)=v.2:=by
    filter_upwards[hYE] with v hv
    have hv' : Y v*C (Y v,v.1)-v.2=0 := by simpa [F] using hv
    exact sub_eq_zero.mp hv'
  have haxisT:Tendsto (fun ν:ℂ=>((ν,0),(0:ℂ))) (𝓝 0) (𝓝 (0:(ℂ × ℂ) × ℂ)):=
    ((continuous_id.prodMk continuous_const).prodMk continuous_const).continuousAt.tendsto
  have hdiagT:Tendsto (fun ν:ℂ=>((ν,ν),x ν)) (𝓝 0) (𝓝 (0:(ℂ × ℂ) × ℂ)):=by
    convert! ((continuous_id.prodMk continuous_id).continuousAt.prodMk hx.continuousAt).tendsto using 1 <;> simp [hx0] <;> rfl
  refine ⟨Y,hY,hY0,hYE',?_⟩
  filter_upwards[haxisT.eventually huniq,hdiagT.eventually huniq,hsaddle] with ν ha hd hs
  refine ⟨ha.mp ?_,hd.mp ?_⟩
  · simp[F]
  · simpa [F] using sub_eq_zero.mpr hs
end WP.Analysis

namespace WP.Analysis
open Filter
open scoped Topology
lemma analytic_inverse_coordinate_unit (C Y:ℂ × ℂ → ℂ)
    (hC:AnalyticAt ℂ C 0) (hY:AnalyticAt ℂ Y 0) (hY0:Y 0=0)
    (haxis:∀ᶠν:ℂ in 𝓝 0,Y (ν,0)=0)
    (hInv:∀ᶠv:ℂ × ℂ in 𝓝 0,Y v*C (Y v,v.1)=v.2):
    ∃q:ℂ × ℂ → ℂ,AnalyticAt ℂ q 0∧
      (∀ᶠv:ℂ × ℂ in 𝓝 0,Y v=v.2*q v∧q v*C (Y v,v.1)=1)∧
      (∀ᶠν:ℂ in 𝓝 0,q (ν,0)=deriv (fun u:ℂ=>Y (ν,u)) 0):=by
  let q:=parameterDifferenceQuotient Y
  have hq:AnalyticAt ℂ q 0:=parameterDifferenceQuotient_analyticAt Y hY
  have hfactor:∀ᶠv:ℂ × ℂ in 𝓝 0,Y v=v.2*q v:=by
    have ht:Tendsto (fun v:ℂ × ℂ=>v.1) (𝓝 0) (𝓝 0):=continuous_fst.continuousAt.tendsto
    filter_upwards[parameterDifferenceQuotient_identity Y hY,ht.eventually haxis] with v hv hzero
    simpa only[hzero,sub_zero] using hv
  have hB:AnalyticAt ℂ (fun v:ℂ × ℂ=>C (Y v,v.1)) 0:=by
    have hh:AnalyticAt ℂ C (Y 0,(0:ℂ × ℂ).1):=by convert! hC using 1 <;> simp [hY0] <;> rfl
    exact hh.comp (f:=fun v:ℂ × ℂ=>(Y v,v.1)) (hY.prod analyticAt_fst)
  have hmul:∀ᶠv:ℂ × ℂ in 𝓝 0,v.2*(q v*C (Y v,v.1))=v.2*(1:ℂ):=by
    filter_upwards[hfactor,hInv] with v hv hi
    calc
      v.2*(q v*C (Y v,v.1))=(v.2*q v)*C (Y v,v.1):=by ring
      _=Y v*C (Y v,v.1):=by rw[←hv]
      _=v.2*1:=by simpa only[mul_one] using hi
  have heq:=analytic_parameter_coordinate_cancel _ (fun _:ℂ × ℂ=>1) (hq.mul hB) analyticAt_const hmul
  refine ⟨q,hq,?_,?_⟩
  · filter_upwards[hfactor,heq] with v hf he
    exact ⟨hf,he⟩
  · have ht:Tendsto (fun ν:ℂ=>(ν,(0:ℂ))) (𝓝 0) (𝓝 (0:ℂ × ℂ)):=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards[ht.eventually hY.eventually_analyticAt] with ν hν
    change parameterDifferenceQuotient Y (ν,0)=_
    rw[parameterDifferenceQuotient_axis,fderiv_axis_eq_deriv_slice Y ν hν]
end WP.Analysis
