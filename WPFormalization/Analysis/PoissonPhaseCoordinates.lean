import WPFormalization.Analysis.PoissonPhasePrecoordinate
import WPFormalization.Analysis.PoissonPhaseInverse
import WPFormalization.Statements.PhaseChangeDefinitions
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma exists_poisson_phase_germ (S:ℂ → ℂ) (hS:AnalyticAt ℂ S 0)
    (hspos:0<(deriv S 0).re):
    ∃x Q:ℂ → ℂ,∃Y q:ℂ × ℂ → ℂ,
      AnalyticAt ℂ x 0∧AnalyticAt ℂ Q 0∧AnalyticAt ℂ Y 0∧AnalyticAt ℂ q 0∧
      x 0=0∧deriv x 0=(deriv S 0)⁻¹∧Q 0=deriv S 0∧Y 0=0∧
      (∀ᶠν:ℂ in 𝓝 0,x ν*deriv S (x ν)=ν∧(ν≠0→Q ν=ν/x ν)∧Y (ν,0)=0∧Y (ν,ν)=x ν)∧
      (∀ᶠv:ℂ × ℂ in 𝓝 0,q v≠0∧Y v=v.2*q v∧
        q v=(if v.2=0 then deriv (fun u:ℂ=>Y (v.1,u)) 0 else Y v/v.2)∧
        S (Y v)-v.2-v.1*Complex.log (q v)=
          S (x v.1)-v.1+v.1*Complex.log (Q v.1)):=by
  obtain ⟨x,Q,C,hx,hQ,hC,hx0,hxd,hQ0,hC0,hsad,hphase⟩:=exists_poisson_phase_precoordinate S hS hspos
  have hCne:C 0≠0:=by rw[hC0];intro h;rw[h,Complex.zero_re] at hspos;exact(lt_irrefl _ hspos)
  obtain ⟨Y,hY,hY0,hInv,haxes⟩:=exists_poisson_phase_inverse C x hC hCne hx hx0
    (by filter_upwards[hsad] with ν hν;exact hν.2.2.2)
  obtain ⟨q,hq,hunit,hqaxis⟩:=analytic_inverse_coordinate_unit C Y hC hY hY0
    (by filter_upwards[haxes] with ν hν;exact hν.1) hInv
  have hMt:Tendsto (fun v:ℂ × ℂ=>(Y v,v.1)) (𝓝 0) (𝓝 (0:ℂ × ℂ)):=by
    convert! (hY.continuousAt.prodMk continuous_fst.continuousAt).tendsto using 1 <;>simp [hY0] <;>rfl
  have hfst:Tendsto (fun v:ℂ × ℂ=>v.1) (𝓝 0) (𝓝 0):=continuous_fst.continuousAt.tendsto
  refine ⟨x,Q,Y,q,hx,hQ,hY,hq,hx0,hxd,hQ0,hY0,?_,?_⟩
  · filter_upwards[hsad,haxes] with ν hs ha
    exact ⟨hs.1,hs.2.2.1,ha.1,ha.2⟩
  · filter_upwards[hunit,hInv,hMt.eventually hphase,hfst.eventually hqaxis] with v hu hi hp ha
    have hqne:q v≠0:=by intro h;rw[h,zero_mul] at hu;exact zero_ne_one hu.2
    have hqi:q v=(C (Y v,v.1))⁻¹:=by
      apply (mul_right_cancel₀ hp.1)
      rw[hu.2,inv_mul_cancel₀ hp.1]
    refine ⟨hqne,hu.1,?_,?_⟩
    · by_cases hz:v.2=0
      · rw[if_pos hz]
        have hv:v=(v.1,0):=Prod.ext rfl hz
        calc q v=q (v.1,0):=congrArg q hv
             _=deriv (fun u:ℂ=>Y (v.1,u)) 0:=ha
      · rw[if_neg hz,hu.1]
        simpa only[mul_comm] using (mul_div_cancel_right₀ (q v) hz).symm
    · simpa only[hi,←hqi] using hp.2
lemma exists_poisson_phase_coordinates (S:ℂ → ℂ) (hS:AnalyticAt ℂ S 0)
    (hspos:0<(deriv S 0).re):
    ∃R:ℝ,0<R∧∃x Q:ℂ → ℂ,∃Z q:ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ x (Metric.ball 0 R)∧AnalyticOnNhd ℂ Q (Metric.ball 0 R)∧
      AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R)∧
      AnalyticOnNhd ℂ q (Metric.ball 0 R ×ˢ Metric.ball 0 R)∧
      x 0=0∧deriv x 0=(deriv S 0)⁻¹∧Q 0=deriv S 0∧Z 0=0∧
      (∀ν:ℂ,‖ν‖<R→x ν*deriv S (x ν)=ν∧(ν≠0→Q ν=ν/x ν)∧Z (0,ν)=0∧Z (ν,ν)=x ν)∧
      (∀u ν:ℂ,‖u‖<R→‖ν‖<R→
        phaseQuotient Z u ν=q (u,ν)∧q (u,ν)≠0∧Z (u,ν)=u*q (u,ν)∧
        S (Z (u,ν))-u-ν*Complex.log (q (u,ν))=
          S (x ν)-ν+ν*Complex.log (Q ν)):=by
  obtain ⟨x,Q,Y,q0,hx,hQ,hY,hq0,hx0,hxd,hQ0,hY0,haxes,hphase⟩:=exists_poisson_phase_germ S hS hspos
  let swap:ℂ × ℂ → ℂ × ℂ:=fun v=>(v.2,v.1)
  have hswap:AnalyticAt ℂ swap 0:=analyticAt_snd.prod analyticAt_fst
  have hswap0:swap 0=0:=by rfl
  let Z:ℂ × ℂ → ℂ:=fun v=>Y (swap v)
  let q:ℂ × ℂ → ℂ:=fun v=>q0 (swap v)
  have hZ:AnalyticAt ℂ Z 0:=by
    have hh:AnalyticAt ℂ Y (swap 0):=by rw[hswap0];exact hY
    exact hh.comp (f:=swap) hswap
  have hq:AnalyticAt ℂ q 0:=by
    have hh:AnalyticAt ℂ q0 (swap 0):=by rw[hswap0];exact hq0
    exact hh.comp (f:=swap) hswap
  have hν:∀ᶠν:ℂ in 𝓝 0,AnalyticAt ℂ x ν∧AnalyticAt ℂ Q ν∧
      x ν*deriv S (x ν)=ν∧(ν≠0→Q ν=ν/x ν)∧Z (0,ν)=0∧Z (ν,ν)=x ν:=by
    filter_upwards[hx.eventually_analyticAt,hQ.eventually_analyticAt,haxes] with ν h1 h2 ha
    exact ⟨h1,h2,ha⟩
  have hswapt:Tendsto swap (𝓝 0) (𝓝 0):=by simpa only[hswap0] using hswap.continuousAt.tendsto
  have hp:∀ᶠv:ℂ × ℂ in 𝓝 0,AnalyticAt ℂ Z v∧AnalyticAt ℂ q v∧
      phaseQuotient Z v.1 v.2=q v∧q v≠0∧Z v=v.1*q v∧
      S (Z v)-v.1-v.2*Complex.log (q v)=S (x v.2)-v.2+v.2*Complex.log (Q v.2):=by
    filter_upwards[hZ.eventually_analyticAt,hq.eventually_analyticAt,hswapt.eventually hphase] with v h1 h2 hp
    refine ⟨h1,h2,?_,hp.1,hp.2.1,hp.2.2.2⟩
    exact hp.2.2.1.symm
  obtain ⟨r1,hr1,hball1⟩:=Metric.eventually_nhds_iff.mp hν
  obtain ⟨r2,hr2,hball2⟩:=Metric.eventually_nhds_iff.mp hp
  let R:=min r1 r2
  have hR:0<R:=lt_min hr1 hr2
  have hv(u ν:ℂ) (hu:‖u‖<R) (hν:‖ν‖<R):‖(u,ν)‖<r2:=by
    rw[Prod.norm_def]
    exact (max_lt hu hν).trans_le (min_le_right r1 r2)
  have hP(u ν:ℂ) (hu:‖u‖<R) (hν:‖ν‖<R):=
    hball2 (by simpa only[dist_zero_right] using hv u ν hu hν)
  have hN(ν:ℂ) (hν:‖ν‖<R):=hball1 (by simpa only[dist_zero_right] using hν.trans_le (min_le_left r1 r2))
  refine ⟨R,hR,x,Q,Z,q,?_,?_,?_,?_,hx0,hxd,hQ0,?_,?_,?_⟩
  · intro ν hν
    exact (hN ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).1
  · intro ν hν
    exact (hN ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).2.1
  · intro v hv
    exact (hP v.1 v.2 (by simpa only[Metric.mem_ball,dist_zero_right] using hv.1)
      (by simpa only[Metric.mem_ball,dist_zero_right] using hv.2)).1
  · intro v hv
    exact (hP v.1 v.2 (by simpa only[Metric.mem_ball,dist_zero_right] using hv.1)
      (by simpa only[Metric.mem_ball,dist_zero_right] using hv.2)).2.1
  · change Y (swap 0)=0
    rw[hswap0,hY0]
  · intro ν hν
    exact (hN ν hν).2.2
  · intro u ν hu hν
    exact (hP u ν hu hν).2.2
end WP.Analysis
