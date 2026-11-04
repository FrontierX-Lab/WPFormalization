import WPFormalization.Analysis.ParameterHadamard
import WPFormalization.Analysis.PoissonSaddleCoordinate
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma analytic_second_saddle_remainder (S:ℂ → ℂ) (hS:AnalyticAt ℂ S 0)
    (x:ℂ → ℂ) (hx:AnalyticAt ℂ x 0) (hx0:x 0=0):
    ∃D:ℂ × ℂ → ℂ,AnalyticAt ℂ D 0∧D 0=iteratedDeriv 2 S 0/2∧
      ∀ᶠv:ℂ × ℂ in 𝓝 0,
        S v.1-S (x v.2)-(v.1-x v.2)*deriv S (x v.2)=
          (v.1-x v.2)^2*D v:=by
  let F:ℂ × ℂ → ℂ:=fun v=>S (x v.1+v.2)-S (x v.1)-v.2*deriv S (x v.1)
  have hxf:AnalyticAt ℂ (fun v:ℂ × ℂ=>x v.1) 0:=hx.comp (f:=fun v:ℂ × ℂ=>v.1) analyticAt_fst
  have hSc:AnalyticAt ℂ S (x 0):=by simpa only[hx0] using hS
  have hSd:AnalyticAt ℂ (deriv S) (x 0):=by simpa only[hx0] using hS.deriv
  have hDSx:AnalyticAt ℂ (fun v:ℂ × ℂ=>deriv S (x v.1)) 0:=by
    simpa only[Function.comp_def] using
      (AnalyticAt.comp (g:=deriv S) (f:=fun v:ℂ × ℂ=>x v.1) (x:=(0:ℂ × ℂ)) hSd hxf)
  have hF:AnalyticAt ℂ F 0:=by
    apply AnalyticAt.sub
    · apply AnalyticAt.sub
      · have hA:AnalyticAt ℂ S (x 0+0):=by simpa only[hx0,zero_add] using hS
        exact hA.comp (f:=fun v:ℂ × ℂ=>x v.1+v.2) (hxf.add analyticAt_snd)
      · exact hSc.comp (f:=fun v:ℂ × ℂ=>x v.1) hxf
    · exact analyticAt_snd.mul hDSx
  have haxis:∀ᶠν:ℂ in 𝓝 0,F (ν,0)=0:=by filter_upwards with ν;simp[F]
  have hxt:Tendsto x (𝓝 0) (𝓝 0):=by simpa only[hx0] using hx.continuousAt.tendsto
  have hderiv:∀ᶠν:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (ν,u)) 0=0:=by
    filter_upwards[hxt.eventually hS.eventually_analyticAt] with ν hν
    have hi:HasDerivAt (fun u:ℂ=>S (x ν+u)) (deriv S (x ν)) 0:=by
      have hh:HasDerivAt S (deriv S (x ν)) (x ν+0):=by simpa only[add_zero] using hν.differentiableAt.hasDerivAt
      convert! hh.comp 0 ((hasDerivAt_const 0 (x ν)).add (hasDerivAt_id 0)) using 1 <;>
        simp only[Pi.add_apply,id_eq,zero_add,mul_one]
    have hd:=(hi.sub (hasDerivAt_const 0 (S (x ν)))).sub ((hasDerivAt_id (0:ℂ)).mul_const (deriv S (x ν)))
    simpa only[F,Pi.sub_def,id_eq,sub_zero,one_mul,sub_self] using hd.deriv
  obtain ⟨G,hG,hG0,hfac⟩:=exists_analytic_parameter_square_factor_with_value F hF haxis hderiv
  have hjet:iteratedDeriv 2 (fun u:ℂ=>F (0,u)) 0=iteratedDeriv 2 S 0:=by
    have he:(fun u:ℂ=>F (0,u))=(fun u:ℂ=>S u-S 0-u*deriv S 0):=by funext u;simp[F,hx0]
    have h1:ContDiffAt ℂ 2 (fun u:ℂ=>S u-S 0) 0:=by
      simpa only[Pi.sub_def] using (hS.sub (analyticAt_const (v:=S 0))).contDiffAt (n:=2)
    have h2:ContDiffAt ℂ 2 (fun u:ℂ=>u*deriv S 0) 0:=by fun_prop
    rw[he,iteratedDeriv_fun_sub h1 h2,
      iteratedDeriv_fun_sub (f:=S) (g:=fun _:ℂ=>S 0) hS.contDiffAt (by fun_prop),iteratedDeriv_mul_const_field]
    norm_num[iteratedDeriv_const,iteratedDeriv_fun_id_zero]
  let M:ℂ × ℂ → ℂ × ℂ:=fun v=>(v.2,v.1-x v.2)
  have hM:AnalyticAt ℂ M 0:=analyticAt_snd.prod (analyticAt_fst.sub (hx.comp (f:=fun v:ℂ × ℂ=>v.2) analyticAt_snd))
  have hM0:M 0=0:=by simp[M,hx0]
  let D:ℂ × ℂ → ℂ:=fun v=>G (M v)
  have hD:AnalyticAt ℂ D 0:=by
    have hh:AnalyticAt ℂ G (M 0):=by rw[hM0];exact hG
    exact hh.comp (f:=M) hM
  have hMt:Tendsto M (𝓝 0) (𝓝 0):=by simpa only[hM0] using hM.continuousAt.tendsto
  refine ⟨D,hD,?_,?_⟩
  · dsimp[D]
    rw[hM0,hG0,hjet]
  · filter_upwards[hMt.eventually hfac] with v hv
    have he:x v.2+(v.1-x v.2)=v.1:=by ring
    simpa only[F,M,D,he] using hv
end WP.Analysis
