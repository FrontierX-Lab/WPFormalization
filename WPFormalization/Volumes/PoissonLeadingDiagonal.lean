import WPFormalization.Analysis.PoissonPhaseSecondDerivative
import WPFormalization.Analysis.RemovablePhaseQuotient
import WPFormalization.Volumes.OriginSaddleMatching
import WPFormalization.HigherOrder.PoissonFamilyCoefficients
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma physicalDensitySaddle_spec (ν:ℝ) (hν:0<ν):
    XR (densityY (2*ν))∈Ioo (0:ℝ) xCritical∧WP.Psi (XR (densityY (2*ν)))=ν:=by
  have hy:=densityY_spec (2*ν) (by linarith)
  have hYp:0<densityY (2*ν):=by
    by_contra h
    have hz:densityY (2*ν)=0:=le_antisymm (not_lt.mp h) hy.1.1
    rw[hz,density_zero_value] at hy
    linarith[hy.2]
  have hx0:0<XR (densityY (2*ν)):=by
    rw[←XR_zero]
    exact XR_strictMonoOn y₀_pos.le hy.1.2.le hYp
  have hxc:XR (densityY (2*ν))<xCritical:=XR_strictMonoOn hy.1.2.le (Set.mem_Iic.mpr (le_refl y₀)) hy.1.2
  have hInv:inverseY (XR (densityY (2*ν)))=densityY (2*ν):=inverseY_eq_of_root _ _ hy.1.2.le rfl
  refine ⟨⟨hx0,hxc⟩,?_⟩
  rw[WP.Psi,hInv,hy.2]
  ring
lemma densitySaddle_tendsto_zero_right:
    Tendsto (fun ν:ℝ=>XR (densityY (2*ν))) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℝ)):=by
  have hT2:Tendsto (fun ν:ℝ=>2*ν) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)):=by
    convert! (continuous_const.mul continuous_id).continuousAt.tendsto (x:=(0:ℝ)) using 1 <;>simp
  have hTw:Tendsto (fun ν:ℝ=>2*ν) (𝓝[≥] (0:ℝ)) (𝓝[≥] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hT2.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards[self_mem_nhdsWithin] with ν hν
    change 0≤ν at hν
    change 0≤2*ν
    linarith
  simpa only[Function.comp_def,XR_zero] using
    XR_continuous.continuousAt.tendsto.comp (densityY_tendsto_zero_right.comp hTw)
lemma poisson_phase_leading_diagonal_germ (S xco Q:ℂ→ℂ) (Z:ℂ × ℂ → ℂ)
    (R:ℝ) (hR:0<R) (hS:AnalyticAt ℂ S 0) (hSd:deriv S 0≠0)
    (hxco:AnalyticAt ℂ xco 0) (hxco0:xco 0=0)
    (hZ:AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (haxes:∀ν:ℂ,‖ν‖<R→xco ν*deriv S (xco ν)=ν∧Z (0,ν)=0∧Z (ν,ν)=xco ν)
    (hphase:∀u ν:ℂ,‖u‖<R→‖ν‖<R→phaseQuotient Z u ν≠0∧
      S (Z (u,ν))-u-ν*Complex.log (phaseQuotient Z u ν)=S (xco ν)-ν+ν*Complex.log (Q ν))
    (hEuler:∀ᶠx:ℝ in 𝓝 0,0≤x→(x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ)):
    ∀ᶠν:ℝ in 𝓝[≥] (0:ℝ),0<ν→phaseAmplitude Z (fun _:ℂ=>1) ((ν:ℂ),(ν:ℂ))=
      ((Real.sqrt (ν/WP.euler WP.Psi (XR (densityY (2*ν)))):ℝ):ℂ):=by
  have hp0:(0:ℂ × ℂ)∈Metric.ball (0:ℂ) R ×ˢ Metric.ball (0:ℂ) R:=by
    constructor <;> simpa only[Metric.mem_ball,dist_zero_right,Prod.fst_zero,Prod.snd_zero,norm_zero] using hR
  have hZ0:Z 0=0:=(haxes 0 (by simpa only[norm_zero] using hR)).2.1
  have hq0:phaseQuotient Z 0 0≠0:=(hphase 0 0 (by simpa only[norm_zero] using hR) (by simpa only[norm_zero] using hR)).1
  have hsaddle:∀ᶠν:ℂ in 𝓝 0,xco ν*deriv S (xco ν)=ν:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hR] with ν hν
    exact (haxes ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).1
  have haxis:∀ᶠν:ℂ in 𝓝 0,Z (0,ν)=0:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hR] with ν hν
    exact (haxes ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).2.1
  have hU:=phaseAmplitude_one_analyticAt_zero_of_axis Z (hZ 0 hp0) haxis hq0
  let J:ℂ→ℂ:=fun ν=>phaseAmplitude Z (fun _:ℂ=>1) (ν,ν)
  have hJ:AnalyticAt ℂ J 0:=by
    convert! hU.comp (f:=fun ν:ℂ=>(ν,ν)) (analyticAt_id.prod analyticAt_id) using 1 <;>rfl
  have hJ0:J 0=1:=phaseAmplitude_at_origin Z _ hZ0 hq0
  have hJRe:∀ᶠν:ℂ in 𝓝 0,0<(J ν).re:=
    (Complex.continuous_re.continuousAt.comp (f:=J) hJ.continuousAt).tendsto.eventually
      (eventually_gt_nhds (by change 0<(J 0).re;rw[hJ0,Complex.one_re];norm_num))
  have hreal:Tendsto (fun ν:ℝ=>(ν:ℂ)) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℂ)):=by
    have ht:=Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ))
    simpa only[Complex.ofReal_zero] using ht.mono_left nhdsWithin_le_nhds
  have hX:=densitySaddle_tendsto_zero_right
  have hXc:Tendsto (fun ν:ℝ=>(XR (densityY (2*ν)):ℂ)) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℂ)):=by
    have ht:=Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ)) |>.comp hX
    simpa only[Function.comp_def,Complex.ofReal_zero] using ht
  filter_upwards[origin_saddle_matches_densityY S xco hS hSd hxco hxco0 hsaddle hEuler,
    hreal.eventually hJRe,hXc.eventually hS.eventually_analyticAt,hX.eventually hEuler.eventually_nhds,
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with ν hmatch hjre hsx heLocal hνR hν
  let x:ℝ:=XR (densityY (2*ν))
  have hx:x∈Ioo (0:ℝ) xCritical:=(physicalDensitySaddle_spec ν hν).1
  have hn:‖(ν:ℂ)‖<R:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos hν] using hνR
  have hn0:(ν:ℂ)≠0:=by exact_mod_cast hν.ne'
  have hx0:(x:ℂ)≠0:=by exact_mod_cast hx.1.ne'
  let z:ℂ→ℂ:=fun u=>Z (u,(ν:ℂ))
  have hz:AnalyticAt ℂ z (ν:ℂ):=(hZ ((ν:ℂ),(ν:ℂ))
    ⟨by simpa only[Metric.mem_ball,dist_zero_right] using hn,by simpa only[Metric.mem_ball,dist_zero_right] using hn⟩).comp
    (f:=fun u:ℂ=>(u,(ν:ℂ))) (analyticAt_id.prod analyticAt_const)
  have hzv:z (ν:ℂ)=(x:ℂ):=(haxes (ν:ℂ) hn).2.2.trans hmatch
  have hst:(x:ℂ)*deriv S (x:ℂ)=(ν:ℂ):=by
    simpa only[hmatch] using (haxes (ν:ℂ) hn).1
  have hph:∀ᶠu:ℂ in 𝓝 (ν:ℂ),S (z u)-u-(ν:ℂ)*Complex.log (z u/u)=
      S (xco (ν:ℂ))-(ν:ℂ)+(ν:ℂ)*Complex.log (Q (ν:ℂ)):=by
    have hνb:(ν:ℂ)∈Metric.ball (0:ℂ) R:=by simpa only[Metric.mem_ball,dist_zero_right] using hn
    filter_upwards[Metric.isOpen_ball.mem_nhds hνb,
      eventually_ne_nhds hn0] with u hu hun
    have hp:=(hphase u (ν:ℂ) (by simpa only[Metric.mem_ball,dist_zero_right] using hu) hn).2
    simpa only[phaseQuotient,if_neg hun] using hp
  have he:(fun t:ℝ=>(t:ℂ)*deriv S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(WP.Psi t:ℂ)):=by
    filter_upwards[heLocal,eventually_gt_nhds hx.1] with t ht htp
    exact ht htp.le
  have hsq:=poisson_phase_diagonal_jacobian_square S z ν x _ hν hx hsx hz hzv hst hph he
  have hJe:J (ν:ℂ)=(ν:ℂ)*deriv z (ν:ℂ)/(x:ℂ):=by
    simp only[J,phaseAmplitude,one_mul,phaseQuotient,if_neg hn0]
    rw[show Z ((ν:ℂ),(ν:ℂ))=(x:ℂ) from hzv]
    change deriv z (ν:ℂ)/((x:ℂ)/(ν:ℂ))=(ν:ℂ)*deriv z (ν:ℂ)/(x:ℂ)
    field_simp
  have hjsq:(J (ν:ℂ))^2=((ν/WP.euler WP.Psi x:ℝ):ℂ):=by rw[hJe];exact hsq
  exact complex_eq_sqrt_of_square (J (ν:ℂ)) _ hjre hjsq
end WP.Analysis
