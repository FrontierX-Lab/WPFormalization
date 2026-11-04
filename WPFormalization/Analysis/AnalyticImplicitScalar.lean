import WPFormalization.Analysis.ImplicitBranch
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology ContDiff
lemma exists_analytic_implicit_scalar
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F:E × ℂ → ℂ) (p:E × ℂ) (hF:AnalyticAt ℂ F p)
    (hInv:(fderiv ℂ F p ∘L ContinuousLinearMap.inr ℂ E ℂ).IsInvertible):
    ∃ψ:E→ℂ,AnalyticAt ℂ ψ p.1 ∧ ψ p.1=p.2 ∧
      (∀ᶠx in 𝓝 p.1,F (x,ψ x)=F p) ∧
      (∀ᶠq in 𝓝 p,F q=F p↔ψ q.1=q.2) ∧
      HasStrictFDerivAt ψ
        (-(fderiv ℂ F p ∘L ContinuousLinearMap.inr ℂ E ℂ).inverse ∘L
          (fderiv ℂ F p ∘L ContinuousLinearMap.inl ℂ E ℂ)) p.1:=by
  have hn:(ω:ℕ∞ω)≠0:=by simp
  have hc:ContDiffAt ℂ ω F p:=hF.contDiffAt
  refine ⟨hc.implicitFunction hn hInv,?_,hc.implicitFunction_apply_self hn hInv,
    hc.eventually_apply_implicitFunction hn hInv,hc.eventually_apply_eq_iff_implicitFunction hn hInv,
    hc.hasStrictFDerivAt_implicitFunction hn hInv⟩
  exact (hc.contDiffAt_implicitFunction hn hInv).analyticAt
end WP.Analysis
