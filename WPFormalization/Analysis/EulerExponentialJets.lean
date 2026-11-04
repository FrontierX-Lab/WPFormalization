import WPFormalization.Statements.ParameterDefinitions
import WPFormalization.Analysis.Taylor
/-! Exact exponential-tilt Taylor jets and real traces of all Euler iterates.
Complex analytic germs supply genuine one-variable derivatives; agreement with
the real germ identifies every Euler jet, retaining the actual Euler operator.
These formulas support both physical centered phases and the original CG3 recipe. -/
noncomputable section
open Filter
open scoped Topology
namespace WP.Analysis
def complexEuler (f:ℂ → ℂ) (z:ℂ):ℂ:=z*deriv f z
lemma complexEuler_analyticAt (f:ℂ → ℂ) (z:ℂ) (hf:AnalyticAt ℂ f z):
    AnalyticAt ℂ (complexEuler f) z := analyticAt_id.mul hf.deriv
lemma complex_exponential_tilt_deriv (f:ℂ → ℂ) (x c:ℂ) (hf:AnalyticAt ℂ f x) :
    deriv (fun τ:ℂ=>f (x*Complex.exp (c*τ))) =ᶠ[𝓝 0]
      (fun τ:ℂ=>c*complexEuler f (x*Complex.exp (c*τ))) := by
  have ht:Tendsto (fun τ:ℂ=>x*Complex.exp (c*τ)) (𝓝 0) (𝓝 x) := by
    have hc:ContinuousAt (fun τ:ℂ=>x*Complex.exp (c*τ)) 0 := by fun_prop
    simpa only [mul_zero,Complex.exp_zero,mul_one] using hc.tendsto
  filter_upwards [ht.eventually hf.eventually_analyticAt] with τ hτ
  have hz:HasDerivAt (fun τ:ℂ=>x*Complex.exp (c*τ)) (c*(x*Complex.exp (c*τ))) τ := by
    convert! (((Complex.hasDerivAt_exp (c*τ)).comp τ ((hasDerivAt_id τ).const_mul c)).const_mul x) using 1
    ring
  have hd:=hτ.differentiableAt.hasDerivAt.comp τ hz
  convert! hd.deriv using 1
  dsimp only [complexEuler]
  ring
lemma iteratedDeriv_exponential_tilt (f:ℂ → ℂ) (x c:ℂ) (hf:AnalyticAt ℂ f x) (n:ℕ) :
    iteratedDeriv n (fun τ:ℂ=>f (x*Complex.exp (c*τ))) 0=
      c^n*((complexEuler^[n]) f) x := by
  induction n generalizing f with
  | zero=>simp
  | succ n ih=>
    rw [iteratedDeriv_succ',(complex_exponential_tilt_deriv f x c hf).iteratedDeriv_eq n,
      iteratedDeriv_const_mul_field,ih (complexEuler f) (complexEuler_analyticAt f x hf),
      Function.iterate_succ_apply,pow_succ]
    ring
lemma coeff_exponential_tilt (f:ℂ → ℂ) (x c:ℂ) (hf:AnalyticAt ℂ f x) (n:ℕ) :
    WP.coeff (fun τ:ℂ=>f (x*Complex.exp (c*τ))) n=
      c^n*((complexEuler^[n]) f) x/(n.factorial:ℂ) := by
  rw [WP.coeff,iteratedDeriv_exponential_tilt f x c hf n]
lemma complex_deriv_real_trace (f:ℂ → ℂ) (g:ℝ → ℝ) (x:ℝ)
    (hf:DifferentiableAt ℂ f (x:ℂ)) (hg:DifferentiableAt ℝ g x)
    (htrace:(fun t:ℝ=>f (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(g t:ℂ))) :
    deriv f (x:ℂ)=((deriv g x:ℝ):ℂ) := by
  have hd:HasDerivAt (fun t:ℝ=>(g t:ℂ)) (deriv f (x:ℂ)) x :=
    hf.hasDerivAt.comp_ofReal.congr_of_eventuallyEq htrace.symm
  exact hd.unique hg.hasDerivAt.ofReal_comp
lemma complexEuler_real_trace_germ (f:ℂ → ℂ) (g:ℝ → ℝ) (x:ℝ)
    (hf:AnalyticAt ℂ f (x:ℂ)) (hg:AnalyticAt ℝ g x)
    (htrace:(fun t:ℝ=>f (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(g t:ℂ))) :
    (fun t:ℝ=>complexEuler f (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(WP.euler g t:ℂ)) := by
  have hc:Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝 x) (𝓝 (x:ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto
  filter_upwards [hc.eventually hf.eventually_analyticAt,hg.eventually_analyticAt,htrace.eventually_nhds]
    with t hft hgt htr
  dsimp only [complexEuler,WP.euler]
  rw [complex_deriv_real_trace f g t hft.differentiableAt hgt.differentiableAt htr,
    Complex.ofReal_mul]
lemma iterated_complexEuler_real_trace (f:ℂ → ℂ) (g:ℝ → ℝ) (x:ℝ)
    (hf:AnalyticAt ℂ f (x:ℂ)) (hg:AnalyticAt ℝ g x)
    (htrace:(fun t:ℝ=>f (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(g t:ℂ))) (n:ℕ) :
    ((complexEuler^[n]) f) (x:ℂ)=(((WP.euler^[n]) g) x:ℂ) := by
  induction n generalizing f g with
  | zero=>exact htrace.self_of_nhds
  | succ n ih=>
    have hEf:AnalyticAt ℂ (complexEuler f) (x:ℂ) := complexEuler_analyticAt f (x:ℂ) hf
    have hEg:AnalyticAt ℝ (WP.euler g) x := analyticAt_id.mul hg.deriv
    simpa only [Function.iterate_succ_apply] using ih (complexEuler f) (WP.euler g) hEf hEg
      (complexEuler_real_trace_germ f g x hf hg htrace)
lemma coeff_exponential_tilt_real_jets (f:ℂ → ℂ) (g:ℝ → ℝ) (x:ℝ) (c:ℂ)
    (hf:AnalyticAt ℂ f (x:ℂ)) (hg:AnalyticAt ℝ g x)
    (htrace:(fun t:ℝ=>f (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(g t:ℂ))) (n:ℕ) :
    WP.coeff (fun τ:ℂ=>f ((x:ℂ)*Complex.exp (c*τ))) n=
      c^n*((((WP.euler^[n]) g) x:ℝ):ℂ)/(n.factorial:ℂ) := by
  rw [coeff_exponential_tilt f (x:ℂ) c hf n,iterated_complexEuler_real_trace f g x hf hg htrace n]
end WP.Analysis
