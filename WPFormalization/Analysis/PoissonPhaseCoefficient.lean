import WPFormalization.Analysis.CoefficientSubstitution
import WPFormalization.Statements.PhaseChangeDefinitions
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma poisson_phase_exponential (h:ℂ) (k:ℕ) (ν a u c K:ℂ) (hc:c≠0)
    (hν:(h:ℂ)*ν=(k:ℂ)) (he:a-u-ν*Complex.log c=K):
    Complex.exp ((h:ℂ)*a)=Complex.exp ((h:ℂ)*K)*Complex.exp ((h:ℂ)*u)*c^k:=by
  have ha:(h:ℂ)*a=(h:ℂ)*K+(h:ℂ)*u+(k:ℂ)*Complex.log c:=by
    linear_combination (h:ℂ)*he + Complex.log c*hν
  rw[ha,Complex.exp_add,Complex.exp_add,Complex.exp_nat_mul (Complex.log c) k,Complex.exp_log hc]
lemma poisson_phase_coefficient_identity (S x Q:ℂ → ℂ) (Z q:ℂ × ℂ → ℂ)
    (R:ℝ) (hR:0<R) (hS:AnalyticAt ℂ S 0)
    (hq:AnalyticOnNhd ℂ q (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (hdata:∀u ν:ℂ,‖u‖<R→‖ν‖<R→phaseQuotient Z u ν=q (u,ν)∧q (u,ν)≠0∧
      Z (u,ν)=u*q (u,ν)∧S (Z (u,ν))-u-ν*Complex.log (q (u,ν))=
        S (x ν)-ν+ν*Complex.log (Q ν))
    (H:ℂ → ℂ) (hH:AnalyticAt ℂ H 0) (h:ℂ) (k:ℕ) (hh:h≠0)
    (hν:‖(k:ℂ)/(h:ℂ)‖<R):
    let ν:ℂ:=(k:ℂ)/(h:ℂ)
    WP.coeff (fun z:ℂ=>Complex.exp ((h:ℂ)*S z)*H z) k=
      Complex.exp ((h:ℂ)*(S (x ν)-ν+ν*Complex.log (Q ν)))*
        WP.coeff (fun u:ℂ=>Complex.exp ((h:ℂ)*u)*phaseAmplitude Z H (u,ν)) k:=by
  let ν:ℂ:=(k:ℂ)/(h:ℂ)
  let qs:ℂ → ℂ:=fun u=>q (u,ν)
  have hp:(0,ν)∈Metric.ball (0:ℂ) R ×ˢ Metric.ball (0:ℂ) R:=
    ⟨by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR,
      by simpa only[Metric.mem_ball,dist_zero_right] using hν⟩
  have hqs:AnalyticAt ℂ qs 0:=(hq (0,ν) hp).comp (f:=fun u:ℂ=>(u,ν)) (analyticAt_id.prod analyticAt_const)
  have hqs0:qs 0≠0:=(hdata 0 ν (by simpa only[norm_zero] using hR) hν).2.1
  have hb:∀ᶠu:ℂ in 𝓝 0,‖u‖<R:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hR] with u hu
    simpa only[Metric.mem_ball,dist_zero_right] using hu
  have hfactor:(fun u:ℂ=>Z (u,ν))=ᶠ[𝓝 0] (fun u:ℂ=>u*qs u):=by
    filter_upwards[hb] with u hu
    exact (hdata u ν hu hν).2.2.1
  let G:ℂ → ℂ:=fun z=>Complex.exp ((h:ℂ)*S z)*H z
  have hG:AnalyticAt ℂ G 0:=((analyticAt_const.mul hS).cexp).mul hH
  let K:ℂ:=S (x ν)-ν+ν*Complex.log (Q ν)
  have hv:(h:ℂ)*ν=(k:ℂ):=by dsimp[ν];field_simp
  have he:(fun u:ℂ=>G (u*qs u)*(qs u+u*deriv qs u)/(qs u)^(k+1))=ᶠ[𝓝 0]
      (fun u:ℂ=>Complex.exp ((h:ℂ)*K)*(Complex.exp ((h:ℂ)*u)*phaseAmplitude Z H (u,ν))):=by
    filter_upwards[hb,hfactor,hfactor.deriv,hqs.eventually_analyticAt] with u hu hf hd hqu
    have hp':=hdata u ν hu hν
    have hder:deriv (fun v:ℂ=>Z (v,ν)) u=qs u+u*deriv qs u:=by
      rw[hd]
      simpa only[Pi.mul_def,id_eq,one_mul] using
        ((hasDerivAt_id u).mul hqu.differentiableAt.hasDerivAt).deriv
    have hexp:=poisson_phase_exponential h k ν (S (Z (u,ν))) u (qs u) K hp'.2.1 hv hp'.2.2.2
    change Complex.exp ((h:ℂ)*S (u*qs u))*H (u*qs u)*(qs u+u*deriv qs u)/(qs u)^(k+1)=_
    rw[←hf,hexp]
    dsimp[phaseAmplitude]
    rw[hp'.1,hder]
    have hn:qs u≠0:=hp'.2.1
    change (Complex.exp ((h:ℂ)*K)*Complex.exp ((h:ℂ)*u)*(qs u)^k)*H (Z (u,ν))*(qs u+u*deriv qs u)/(qs u)^(k+1)=
      Complex.exp ((h:ℂ)*K)*(Complex.exp ((h:ℂ)*u)*(H (Z (u,ν))*(qs u+u*deriv qs u)/qs u))
    rw[pow_succ]
    field_simp <;> ring
  have hc:=congrArg (PowerSeries.coeff k) (taylor_congr he)
  simp only[taylor_coeff] at hc
  calc
    WP.coeff G k=WP.coeff (fun u:ℂ=>G (u*qs u)*(qs u+u*deriv qs u)/(qs u)^(k+1)) k:=
      (coeff_analytic_coordinate_substitution G qs hG hqs hqs0 k).symm
    _=Complex.exp ((h:ℂ)*K)*WP.coeff (fun u:ℂ=>Complex.exp ((h:ℂ)*u)*phaseAmplitude Z H (u,ν)) k:=
      hc.trans (coeff_const_mul _ _ k)
end WP.Analysis
