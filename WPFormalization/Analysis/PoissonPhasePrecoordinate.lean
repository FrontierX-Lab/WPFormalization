import WPFormalization.Analysis.PoissonSecondRemainder
import WPFormalization.Analysis.LogOnePlusRemainder
import WPFormalization.Analysis.PoissonPhaseEta
import WPFormalization.Analysis.PoissonPhaseAlgebra
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma exists_poisson_phase_precoordinate (S:ℂ → ℂ) (hS:AnalyticAt ℂ S 0)
    (hspos:0<(deriv S 0).re):
    ∃x Q:ℂ → ℂ,∃C:ℂ × ℂ → ℂ,
      AnalyticAt ℂ x 0∧AnalyticAt ℂ Q 0∧AnalyticAt ℂ C 0∧
      x 0=0∧deriv x 0=(deriv S 0)⁻¹∧Q 0=deriv S 0∧C 0=deriv S 0∧
      (∀ᶠν:ℂ in 𝓝 0,x ν*deriv S (x ν)=ν∧Q ν=deriv S (x ν)∧
        (ν≠0→Q ν=ν/x ν)∧x ν*C (x ν,ν)=ν)∧
      (∀ᶠv:ℂ × ℂ in 𝓝 0,C v≠0∧
        S v.1-v.1*C v-v.2*Complex.log ((C v)⁻¹)=
          S (x v.2)-v.2+v.2*Complex.log (Q v.2)):=by
  obtain ⟨R,hR,x,Q,hxR,hQR,hx0,hxd,hQ0,hsR⟩:=analytic_saddle_coordinate S hS hspos
  have hx:AnalyticAt ℂ x 0:=hxR 0 (by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR)
  have hQ:AnalyticAt ℂ Q 0:=hQR 0 (by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR)
  have hQne:Q 0≠0:=by rw[hQ0];intro h;rw[h,Complex.zero_re] at hspos;exact(lt_irrefl _ hspos)
  have hsad:∀ᶠν:ℂ in 𝓝 0,x ν*deriv S (x ν)=ν∧Q ν=deriv S (x ν)∧(ν≠0→Q ν=ν/x ν):=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hR] with ν hν
    obtain ⟨h1,h2,h3,h4,h5⟩:=hsR ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)
    exact ⟨h1,h2,h5⟩
  obtain ⟨D,hD,hD0,hDphi⟩:=analytic_second_saddle_remainder S hS x hx hx0
  obtain ⟨L,hL,hLog⟩:=analytic_log1p_second_remainder
  obtain ⟨η,hη,hη0,hηE⟩:=exists_poisson_phase_eta x Q D L hx hQ hD hL hx0 hQne
  have hxν:AnalyticAt ℂ (fun v:ℂ × ℂ=>x v.2) 0:=hx.comp (f:=fun v:ℂ × ℂ=>v.2) analyticAt_snd
  have hQν:AnalyticAt ℂ (fun v:ℂ × ℂ=>Q v.2) 0:=hQ.comp (f:=fun v:ℂ × ℂ=>v.2) analyticAt_snd
  let C:ℂ × ℂ → ℂ:=fun v=>Q v.2+(v.1-x v.2)*η v
  have hC:AnalyticAt ℂ C 0:=hQν.add ((analyticAt_fst.sub hxν).mul hη)
  have hC0:C 0=deriv S 0:=by simp[C,hx0,hQ0]
  let a:ℂ × ℂ → ℂ:=fun v=>(v.1-x v.2)*η v/Q v.2
  have ha:AnalyticAt ℂ a 0:=((analyticAt_fst.sub hxν).mul hη).div hQν hQne
  have ha0:a 0=0:=by simp[a,hx0]
  have haT:Tendsto a (𝓝 0) (𝓝 0):=by simpa only[ha0] using ha.continuousAt.tendsto
  have hQre:∀ᶠν:ℂ in 𝓝 0,0<(Q ν).re:=by
    have hc:ContinuousAt (fun ν:ℂ=>(Q ν).re) 0:=Complex.continuous_re.continuousAt.comp (f:=Q) hQ.continuousAt
    exact hc.tendsto.eventually (eventually_gt_nhds (by rw[hQ0];exact hspos))
  have hCre:∀ᶠv:ℂ × ℂ in 𝓝 0,0<(C v).re:=by
    have hc:ContinuousAt (fun v:ℂ × ℂ=>(C v).re) 0:=Complex.continuous_re.continuousAt.comp (f:=C) hC.continuousAt
    exact hc.tendsto.eventually (eventually_gt_nhds (by rw[hC0];exact hspos))
  have hTre:∀ᶠv:ℂ × ℂ in 𝓝 0,0<(1+a v).re:=by
    have hc:ContinuousAt (fun v:ℂ × ℂ=>(1+a v).re) 0:=
      Complex.continuous_re.continuousAt.comp (f:=fun v:ℂ × ℂ=>1+a v) (continuousAt_const.add ha.continuousAt)
    exact hc.tendsto.eventually (eventually_gt_nhds (by simp[ha0]))
  have hsnd:Tendsto (fun v:ℂ × ℂ=>v.2) (𝓝 0) (𝓝 0):=continuous_snd.continuousAt.tendsto
  refine ⟨x,Q,C,hx,hQ,hC,hx0,hxd,hQ0,hC0,?_,?_⟩
  · filter_upwards[hsad] with ν hν
    refine ⟨hν.1,hν.2.1,hν.2.2,?_⟩
    simpa only[C,sub_self,zero_mul,add_zero,hν.2.1] using hν.1
  · filter_upwards[hsnd.eventually hsad,hDphi,hηE,haT.eventually hLog,
      hsnd.eventually hQre,hCre,hTre] with v hs hφ hE hlog hqr hcr htr
    have hcn:C v≠0:=by intro hz;rw[hz,Complex.zero_re] at hcr;exact(lt_irrefl _ hcr)
    refine ⟨hcn,?_⟩
    have hsc:x v.2*Q v.2=v.2:=by simpa only[hs.2.1] using hs.1
    apply poisson_eta_phase_log_identity (S v.1) (S (x v.2)) v.1 (x v.2) (Q v.2) v.2
      (D v) (η v) (L (a v)) hqr hsc
    · simpa only[hs.2.1] using hφ
    · simpa only[a] using hE
    · simpa only[a] using hlog
    · exact htr
    · exact hcr
end WP.Analysis
