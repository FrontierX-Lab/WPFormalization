import WPFormalization.Volumes.ExtractionPhaseEuler
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma origin_saddle_matches_Psi (S xco:ℂ → ℂ) (hS:AnalyticAt ℂ S 0) (hSd:deriv S 0≠0)
    (hxco:AnalyticAt ℂ xco 0) (hxco0:xco 0=0)
    (hsaddle:∀ᶠν:ℂ in 𝓝 0,xco ν*deriv S (xco ν)=ν)
    (hEuler:∀ᶠx:ℝ in 𝓝 0,0≤x→(x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ)):
    ∀ᶠx:ℝ in 𝓝 0,0≤x→xco (WP.Psi x:ℂ)=(x:ℂ):=by
  let F:ℂ → ℂ:=fun z=>z*deriv S z
  have hF:AnalyticAt ℂ F 0:=analyticAt_id.mul hS.deriv
  have hFd:deriv F 0=deriv S 0:=by
    simpa only[F,Pi.mul_def,id_eq,one_mul,zero_mul,add_zero] using
      ((hasDerivAt_id (0:ℂ)).mul hS.deriv.differentiableAt.hasDerivAt).deriv
  have hFn:deriv F 0≠0:=by rw[hFd];exact hSd
  let I:=hF.hasStrictDerivAt.localInverse F (deriv F 0) 0 hFn
  have hleft:∀ᶠz:ℂ in 𝓝 0,I (F z)=z:=hF.hasStrictDerivAt.eventually_left_inverse hFn
  have hPsi:AnalyticAt ℝ WP.Psi 0:=Psi_analyticAt_interior 0 ⟨le_rfl,xCritical_pos_parameter⟩
  have htPsi:Tendsto (fun x:ℝ=>(WP.Psi x:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=by
    have hh:=Complex.continuous_ofReal.continuousAt.comp hPsi.continuousAt |>.tendsto
    simpa only[Function.comp_def,Psi_zero_value,Complex.ofReal_zero] using hh
  have htco:Tendsto (fun x:ℝ=>xco (WP.Psi x:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=by
    simpa only[Function.comp_def,hxco0] using hxco.continuousAt.tendsto.comp htPsi
  have htReal:Tendsto (fun x:ℝ=>(x:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=by
    simpa only[Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ))
  filter_upwards[htco.eventually hleft,htReal.eventually hleft,htPsi.eventually hsaddle,hEuler] with x hc hr hs he hx
  change I (xco (WP.Psi x:ℂ)*deriv S (xco (WP.Psi x:ℂ)))=xco (WP.Psi x:ℂ) at hc
  change I ((x:ℂ)*deriv S (x:ℂ))=(x:ℂ) at hr
  rw[hs] at hc
  rw[he hx] at hr
  exact hc.symm.trans hr
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma densityY_tendsto_zero_right:Tendsto WP.densityY (𝓝[≥] (0:ℝ)) (𝓝 (0:ℝ)):=by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards[self_mem_nhdsWithin] with l hl
    exact ha.trans_le (densityY_spec l hl).1.1
  · intro b hb
    let Y:ℝ:=min (b/2) (y₀/2)
    have hYpos:0<Y:=lt_min (half_pos hb) (half_pos y₀_pos)
    have hYb:Y<b:=(min_le_left _ _).trans_lt (half_lt_self hb)
    have hYy:Y<y₀:=(min_le_right _ _).trans_lt (half_lt_self y₀_pos)
    have hY:Y∈Ico (0:ℝ) y₀:=⟨hYpos.le,hYy⟩
    have hden:0<WP.density Y:=by
      have hh:=density_strictMonoOn ⟨le_rfl,y₀_pos⟩ hY hYpos
      simpa only[WP.density_zero_value] using hh
    filter_upwards[(eventually_lt_nhds hden).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with l hl hl0
    have hd:=densityY_spec l hl0
    by_contra h
    have hYle:Y≤WP.densityY l:=hYb.le.trans (not_lt.mp h)
    have hh:=density_strictMonoOn.monotoneOn hY hd.1 hYle
    rw[hd.2] at hh
    exact (not_lt_of_ge hh) hl
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma origin_saddle_matches_densityY (S xco:ℂ → ℂ) (hS:AnalyticAt ℂ S 0) (hSd:deriv S 0≠0)
    (hxco:AnalyticAt ℂ xco 0) (hxco0:xco 0=0)
    (hsaddle:∀ᶠν:ℂ in 𝓝 0,xco ν*deriv S (xco ν)=ν)
    (hEuler:∀ᶠx:ℝ in 𝓝 0,0≤x→(x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ)):
    ∀ᶠν:ℝ in 𝓝[≥] (0:ℝ),xco (ν:ℂ)=(XR (WP.densityY (2*ν)):ℂ):=by
  have hT2:Tendsto (fun ν:ℝ=>2*ν) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)):=by
    convert! (continuous_const.mul continuous_id).continuousAt.tendsto (x:=(0:ℝ)) using 1 <;>simp
  have hTw:Tendsto (fun ν:ℝ=>2*ν) (𝓝[≥] (0:ℝ)) (𝓝[≥] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hT2.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards[self_mem_nhdsWithin] with ν hν
    change 0≤ν at hν
    change 0≤2*ν
    linarith
  have hYt:Tendsto (fun ν:ℝ=>WP.densityY (2*ν)) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℝ)):=
    densityY_tendsto_zero_right.comp hTw
  have hXt:Tendsto (fun ν:ℝ=>XR (WP.densityY (2*ν))) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℝ)):=by
    simpa only[Function.comp_def,XR_zero] using XR_continuous.continuousAt.tendsto.comp hYt
  filter_upwards[hXt.eventually (origin_saddle_matches_Psi S xco hS hSd hxco hxco0 hsaddle hEuler),
    self_mem_nhdsWithin] with ν hm hν
  have hν0:0≤ν:=hν
  have hl:0≤2*ν:=by linarith
  have hy:=densityY_spec (2*ν) hl
  have hx0:0≤XR (WP.densityY (2*ν)):=by
    rw[←XR_zero]
    exact XR_strictMonoOn.monotoneOn y₀_pos.le hy.1.2.le hy.1.1
  have hInv:inverseY (XR (WP.densityY (2*ν)))=WP.densityY (2*ν):=
    inverseY_eq_of_root _ _ hy.1.2.le rfl
  have hPsi:WP.Psi (XR (WP.densityY (2*ν)))=ν:=by
    rw[WP.Psi,hInv,hy.2]
    ring
  simpa only[hPsi] using hm hx0
end WP.Analysis
