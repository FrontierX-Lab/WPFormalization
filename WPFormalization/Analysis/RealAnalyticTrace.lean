import WPFormalization.Analysis.Taylor
/-! A holomorphic germ agreeing with a real function gives its genuine real analytic germ. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma analyticAt_real_of_complex_trace (f:ℂ → ℂ) (g:ℝ → ℝ) (x:ℝ)
    (hf:AnalyticAt ℂ f (x:ℂ))
    (htrace:(fun t:ℝ=>f (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(g t:ℂ))) : AnalyticAt ℝ g x := by
  have hfR:AnalyticAt ℝ f (x:ℂ):=hf.restrictScalars
  have hcomp:AnalyticAt ℝ (fun t:ℝ=>f (t:ℂ)) x:=
    hfR.comp (f:=fun t:ℝ=>(t:ℂ)) (Complex.ofRealCLM.analyticAt x)
  have hRe:AnalyticAt ℝ (fun t:ℝ=>(f (t:ℂ)).re) x:=
    (Complex.reCLM.analyticAt (f (x:ℂ))).comp (f:=fun t:ℝ=>f (t:ℂ)) hcomp
  apply hRe.congr
  filter_upwards[htrace] with t ht
  rw[ht,Complex.ofReal_re]
end WP.Analysis
