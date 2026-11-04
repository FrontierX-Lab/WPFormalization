import Mathlib
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma analytic_saddle_coordinate (S:ℂ→ℂ) (hS:AnalyticAt ℂ S 0)
    (hspos:0<(deriv S 0).re):
    ∃R:ℝ,0<R∧∃x Q:ℂ→ℂ,
      AnalyticOnNhd ℂ x (Metric.ball 0 R)∧
      AnalyticOnNhd ℂ Q (Metric.ball 0 R)∧
      x 0=0∧deriv x 0=(deriv S 0)⁻¹∧Q 0=deriv S 0∧
      (∀ν:ℂ,‖ν‖<R→x ν*deriv S (x ν)=ν∧Q ν=deriv S (x ν)∧
        Q ν≠0∧Q ν∈Complex.slitPlane∧(ν≠0→Q ν=ν/x ν)):=by
  let q:ℂ→ℂ:=fun z=>z*deriv S z
  have hqa:AnalyticAt ℂ q 0:=analyticAt_id.mul hS.deriv
  have hq0:q 0=0:=by simp[q]
  have hqD:HasDerivAt q (deriv S 0) 0:=by
    convert! (hasDerivAt_id (0:ℂ)).mul hS.deriv.differentiableAt.hasDerivAt using 1 <;>
      simp only[q,id_eq,Pi.mul_apply,one_mul,zero_mul,add_zero]
  have hsne:deriv S 0≠0:=by intro hn;rw[hn,Complex.zero_re] at hspos;exact(lt_irrefl 0 hspos)
  have hqne:deriv q 0≠0:=by rwa[hqD.deriv]
  let x:ℂ→ℂ:=hqa.hasStrictDerivAt.localInverse q (deriv q 0) 0 hqne
  have hxa:AnalyticAt ℂ x 0:=by simpa only[hq0] using hqa.analyticAt_localInverse hqne
  have hx0:x 0=0:=by
    simpa only[hq0] using (hqa.hasStrictDerivAt.eventually_left_inverse hqne).self_of_nhds
  have hxd:deriv x 0=(deriv S 0)⁻¹:=by
    have hh:=hqa.hasStrictDerivAt.to_localInverse hqne |>.hasDerivAt
    simpa only[hq0,hqD.deriv] using hh.deriv
  let Q:ℂ→ℂ:=fun ν=>deriv S (x ν)
  have hQa:AnalyticAt ℂ Q 0:=by
    have hh:AnalyticAt ℂ (deriv S) (x 0):=by simpa only[hx0] using hS.deriv
    exact hh.comp hxa
  have hQ0:Q 0=deriv S 0:=by simp only[Q,hx0]
  have hQne:Q 0≠0:=by rwa[hQ0]
  have hQslit:Q 0∈Complex.slitPlane:=by rw[hQ0];exact Or.inl hspos
  have hxright:∀ᶠν:ℂ in 𝓝 0,q (x ν)=ν:=by
    simpa only[hq0] using hqa.hasStrictDerivAt.eventually_right_inverse hqne
  have he:∀ᶠν:ℂ in 𝓝 0,AnalyticAt ℂ x ν∧AnalyticAt ℂ Q ν∧q (x ν)=ν∧Q ν≠0∧Q ν∈Complex.slitPlane:=by
    filter_upwards[hxa.eventually_analyticAt,hQa.eventually_analyticAt,hxright,
      hQa.continuousAt.eventually_ne hQne,hQa.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hQslit)]
      with ν hxa' hQa' hr hne hslit
    exact ⟨hxa',hQa',hr,hne,hslit⟩
  obtain ⟨R,hR,he⟩:=Metric.eventually_nhds_iff.mp he
  have heR(ν:ℂ)(hν:‖ν‖<R):AnalyticAt ℂ x ν∧AnalyticAt ℂ Q ν∧q (x ν)=ν∧Q ν≠0∧Q ν∈Complex.slitPlane:=
    he (by simpa only[dist_zero_right] using hν)
  refine ⟨R,hR,x,Q,(fun ν hν=>(heR ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).1),
    (fun ν hν=>(heR ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).2.1),hx0,hxd,hQ0,?_⟩
  intro ν hν
  obtain ⟨_,_,hr,hne,hslit⟩:=heR ν hν
  change x ν*deriv S (x ν)=ν at hr
  refine ⟨hr,rfl,hne,hslit,?_⟩
  intro hνne
  have hxn:x ν≠0:=by intro hn;rw[hn,zero_mul] at hr;exact hνne hr.symm
  apply (eq_div_iff hxn).2
  simpa only[Q,mul_comm] using hr
end WP.Analysis
