import Mathlib
/-! A native holomorphic germ of a genuine real analytic scalar function. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma realAnalyticAt_complex_germ (f:ℝ→ℝ)(x:ℝ)(hf:AnalyticAt ℝ f x):
    ∃F:ℂ→ℂ,AnalyticAt ℂ F (x:ℂ) ∧
      (fun t:ℝ=>F (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(f t:ℂ)):=by
  let c:ℕ→ℝ:=fun n=>iteratedDeriv n f x/(n.factorial:ℝ)
  let pR:=FormalMultilinearSeries.ofScalars ℝ c
  let pC:=FormalMultilinearSeries.ofScalars ℂ (fun n=>(c n:ℂ))
  have hr:pC.radius=pR.radius:=by
    dsimp[pC,pR,FormalMultilinearSeries.radius]
    simp only[FormalMultilinearSeries.ofScalars_norm,Complex.norm_real]
  have hpR:HasFPowerSeriesAt f pR x:=hf.hasFPowerSeriesAt
  have hpC:0<pC.radius:=by rw[hr];exact hpR.radius_pos
  have hsum:=pC.hasFPowerSeriesOnBall hpC
  let F:ℂ→ℂ:=fun z=>pC.sum (z-(x:ℂ))
  have hF:AnalyticAt ℂ F (x:ℂ):=
    hsum.analyticAt.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  refine ⟨F,hF,?_⟩
  have ht:Tendsto (fun t:ℝ=>(t:ℂ)-(x:ℂ)) (𝓝 x) (𝓝 (0:ℂ)):=by
    simpa only[sub_self] using (show ContinuousAt (fun t:ℝ=>(t:ℂ)-(x:ℂ)) x by fun_prop).tendsto
  filter_upwards[hpR.eventually_hasSum_sub,ht.eventually hsum.eventually_hasSum] with t hR hC
  have hRc:HasSum (fun n:ℕ=>((pR n (fun _=>t-x):ℝ):ℂ)) ((f t:ℝ):ℂ):=Complex.hasSum_ofReal.mpr hR
  have he: (fun n:ℕ=>((pR n (fun _=>t-x):ℝ):ℂ))=
      (fun n:ℕ=>pC n (fun _=>(t:ℂ)-(x:ℂ))):=by
    funext n
    simp only[pR,pC,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,
      Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sub]
  rw[he] at hRc
  simpa only[zero_add,F] using hC.unique hRc
end WP.Analysis
