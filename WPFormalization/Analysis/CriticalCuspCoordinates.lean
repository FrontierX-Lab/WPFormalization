import WPFormalization.Analysis.CriticalParameterAsymptotics
import Mathlib.Analysis.Analytic.Order

/-! The actual quadratic critical cusp-weight difference and its analytic
factor, with the exact second derivative b. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma analytic_quadratic_factor_at_zero (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 0) :
    ∃ B : ℝ → ℝ,AnalyticAt ℝ B 0 ∧ B 0 = iteratedDeriv 2 f 0/2 ∧
      ∀ᶠ δ in 𝓝 0,f δ = δ^2*B δ := by
  obtain ⟨B,hB,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,iteratedDeriv_zero,iteratedDeriv_one,
    h0,h1,smul_eq_mul,mul_zero,zero_add] at he
  refine ⟨B,hB,?_,he⟩
  have heq : f =ᶠ[𝓝 (0:ℝ)] (fun δ => δ^2*B δ) := he
  have hjet := heq.iteratedDeriv_eq 2
  rw [iteratedDeriv_fun_mul (by fun_prop) hB.contDiffAt] at hjet
  norm_num [Finset.sum_range_succ,iteratedDeriv_fun_pow_zero,iteratedDeriv_zero] at hjet
  linarith
/-- The actual cusp-weight difference in the critical coordinate. -/
def criticalXDifference (δ : ℝ) : ℝ := xCritical-XR (y₀-δ)
lemma criticalXDifference_analyticAt : AnalyticAt ℝ criticalXDifference 0 := by
  have hx : AnalyticAt ℝ XR (y₀-(0:ℝ)) := XR_analyticAt _
  exact analyticAt_const.sub (hx.comp (analyticAt_const.sub analyticAt_id))
lemma criticalXDifference_hasDerivAt (δ : ℝ) :
    HasDerivAt criticalXDifference (a (y₀-δ)) δ := by
  have hs : HasDerivAt (fun t : ℝ => y₀-t) (-1) δ := by
    simpa only [zero_sub,id_eq,Pi.sub_apply] using! (hasDerivAt_const δ y₀).sub (hasDerivAt_id δ)
  convert! (hasDerivAt_const δ xCritical).sub ((XR_hasDerivAt (y₀-δ)).comp δ hs) using 1 <;> ring
lemma criticalXDifference_zero : criticalXDifference 0 = 0 := by
  simp only [criticalXDifference,sub_zero,xCritical,sub_self]
lemma criticalXDifference_deriv_zero : deriv criticalXDifference 0 = 0 := by
  rw [(criticalXDifference_hasDerivAt 0).deriv]
  simp only [sub_zero,a,derivX_y₀_zero,Complex.zero_re]
lemma criticalXDifference_second_deriv_zero : iteratedDeriv 2 criticalXDifference 0 = criticalB := by
  have he : deriv criticalXDifference = fun δ => a (y₀-δ) := by
    funext δ
    exact (criticalXDifference_hasDerivAt δ).deriv
  rw [iteratedDeriv_succ,iteratedDeriv_one,he]
  have hs : HasDerivAt (fun δ : ℝ => y₀-δ) (-1) 0 := by
    simpa only [zero_sub,id_eq,Pi.sub_apply] using! (hasDerivAt_const (0:ℝ) y₀).sub (hasDerivAt_id 0)
  have ha : HasDerivAt a ((iteratedDeriv 2 X (y₀:ℂ)).re) (y₀-(0:ℝ)) := by
    simpa only [sub_zero] using WP.a_hasDerivAt y₀
  have hd := ha.comp 0 hs
  simpa only [Function.comp_def,mul_neg_one,criticalB] using hd.deriv
lemma criticalXDifference_factor :
    ∃ B : ℝ → ℝ,AnalyticAt ℝ B 0 ∧ B 0 = criticalB/2 ∧
      ∀ᶠ δ in 𝓝 0,criticalXDifference δ = δ^2*B δ := by
  obtain ⟨B,hB,hB0,he⟩ := analytic_quadratic_factor_at_zero criticalXDifference
    criticalXDifference_analyticAt criticalXDifference_zero criticalXDifference_deriv_zero
  exact ⟨B,hB,by simpa only [criticalXDifference_second_deriv_zero] using hB0,he⟩

end WP.Analysis
