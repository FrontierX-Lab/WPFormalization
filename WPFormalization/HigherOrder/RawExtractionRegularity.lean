import WPFormalization.Analysis.FiniteAnalyticPolynomial
import WPFormalization.Analysis.RealAnalyticComplexGerm
import WPFormalization.Analysis.MarkedTaylorPolynomialJets
import WPFormalization.Volumes.ExtractionLogData
/-! Fixed-order interior regularity of the original CG3 finite extraction recipe.
The original Euler derivatives, variance square root, Gaussian moments and
canonical marked coefficients are retained, with the original marked domain p>=1. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
open WP.HigherOrder
lemma iterated_real_euler_analyticAt (f:ℝ→ℝ)(x:ℝ)(hf:AnalyticAt ℝ f x)(n:ℕ):
    AnalyticAt ℝ ((WP.euler^[n]) f) x:=by
  induction n with
  | zero=>exact hf
  | succ n ih=>
    rw[Function.iterate_succ_apply']
    exact analyticAt_id.mul ih.deriv
lemma actual_extraction_real_analytic_data (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
    AnalyticAt ℝ extractionS x ∧ AnalyticAt ℝ (fun t=>Real.log (extractionB p t)) x ∧
      AnalyticAt ℝ (fun t=>Real.sqrt (WP.euler WP.Psi t)) x ∧
      (∀s,AnalyticAt ℝ (fun t=>markedCoefficient P p s (inverseY t)) x) ∧
      0<WP.euler WP.Psi x:=by
  obtain ⟨S,B,β,hS,hB,hSr,hBr,hv,hβ,hβ0,hphase⟩:=exists_actual_extraction_log_data P p x hx
  have hSa:=analyticAt_real_of_complex_trace S extractionS x hS hSr
  have hBa:=analyticAt_real_of_complex_trace B (fun t=>Real.log (extractionB p t)) x hB hBr
  have hPa:=Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩
  have hVa:AnalyticAt ℝ (WP.euler WP.Psi) x:=analyticAt_id.mul hPa.deriv
  have hroot:=real_sqrt_analyticAt_of_pos _ x hVa hv
  obtain ⟨Γ,hΓ⟩:=canonical_marked_weight_germ_family P p hp x hx
  exact ⟨hSa,hBa,hroot,fun s=>analyticAt_real_of_complex_trace (Γ s) _ x (hΓ s).1 (hΓ s).2,hv⟩
lemma extractionLogPolynomial_finiteAnalyticAt (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(n:ℕ):
    FiniteAnalyticPolynomialAt (fun t=>extractionLogPolynomial p t n) x:=by
  obtain ⟨hS,hB,hroot,hL,hv⟩:=actual_extraction_real_analytic_data P p hp x hx
  have hrootne:Real.sqrt (WP.euler WP.Psi x)≠0:=(Real.sqrt_pos.mpr hv).ne'
  by_cases hn:n=0
  · subst n
    simpa only[extractionLogPolynomial_zero] using FiniteAnalyticPolynomialAt.const (x:=x) 0
  · simp only[extractionLogPolynomial,ite_eq_right hn]
    apply FiniteAnalyticPolynomialAt.add
    · apply FiniteAnalyticPolynomialAt.monomial
      exact (iterated_real_euler_analyticAt _ x hS (n+2)).div
        (analyticAt_const.mul (hroot.pow (n+2))) (by positivity)
    · apply FiniteAnalyticPolynomialAt.monomial
      exact (iterated_real_euler_analyticAt _ x hB n).div
        (analyticAt_const.mul (hroot.pow n)) (by positivity)
lemma extractionExpPolynomial_finiteAnalyticAt (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(n:ℕ):
    FiniteAnalyticPolynomialAt (fun t=>extractionExpPolynomial p t n) x:=by
  unfold extractionExpPolynomial
  apply FiniteAnalyticPolynomialAt.sum
  intro k hk
  apply FiniteAnalyticPolynomialAt.mul (FiniteAnalyticPolynomialAt.const _)
  exact finiteAnalyticPolynomialAt_series_coeff_pow
    (fun t=>PowerSeries.mk (extractionLogPolynomial p t)) x
    (fun n=>by simpa only[PowerSeries.coeff_mk] using extractionLogPolynomial_finiteAnalyticAt P p hp x hx n) k n
lemma markedTaylorPolynomial_finiteAnalyticAt (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(n:ℕ):
    FiniteAnalyticPolynomialAt (fun t=>markedTaylorPolynomial P p t n) x:=by
  obtain ⟨hS,hB,hroot,hL,hv⟩:=actual_extraction_real_analytic_data P p hp x hx
  have hrootne:Real.sqrt (WP.euler WP.Psi x)≠0:=(Real.sqrt_pos.mpr hv).ne'
  unfold markedTaylorPolynomial
  apply FiniteAnalyticPolynomialAt.sum
  intro s hs
  dsimp only
  apply FiniteAnalyticPolynomialAt.monomial
  exact (iterated_real_euler_analyticAt _ x (hL s) (n-2*s)).div
    (analyticAt_const.mul (hroot.pow (n-2*s))) (by positivity)
lemma extractionNumerator_analytic_coefficients (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
    AnalyticSeriesCoefficientsAt (fun t=>extractionNumerator P p t) x:=by
  intro n
  simp only[extractionNumerator,PowerSeries.coeff_mk]
  have hpoly:FiniteAnalyticPolynomialAt
      (fun t=>∑i∈Finset.range (n+1),extractionExpPolynomial p t i*markedTaylorPolynomial P p t (n-i)) x:=
    FiniteAnalyticPolynomialAt.sum _ _ (fun i hi=>
      (extractionExpPolynomial_finiteAnalyticAt P p hp x hx i).mul
      (markedTaylorPolynomial_finiteAnalyticAt P p hp x hx (n-i)))
  exact hpoly.finiteMoment gaussianMoment
lemma extractionDenominator_analytic_coefficients (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
    AnalyticSeriesCoefficientsAt extractionDenominator x:=by
  have hPa:=Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩
  have hY:=(inverseY_branch x ⟨hx.1.le,hx.2⟩)
  have hden:=J_sub_XR_pos_interior _ hY.1
  have hPpos:0<WP.Psi x:=by
    unfold WP.Psi
    rw[density_J_formula_on_domain _ (stationaryParameterDomain_contains _ hY.1),hY.2]
    rw[hY.2] at hden
    exact div_pos (div_pos (mul_pos (by norm_num) hx.1) hden) (by norm_num)
  intro n
  simp only[extractionDenominator,PowerSeries.coeff_mk]
  by_cases hn:Even n
  · simp only[ite_eq_left hn]
    exact analyticAt_const.mul ((hPa.inv hPpos.ne').pow (n/2))
  · simp only[ite_eq_right hn]
    exact analyticAt_const
lemma rawExtractedCoefficient_weight_analyticAt (P:PsiTheory)(p:ℕ)(hp:1≤p)(j:ℕ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
    AnalyticAt ℝ (fun t=>PowerSeries.coeff (2*j) (extractionNumerator P p t*(extractionDenominator t)⁻¹)) x:=by
  exact ((extractionNumerator_analytic_coefficients P p hp x hx).mul
    ((extractionDenominator_analytic_coefficients x hx).inv (by rw[extractionDenominator_constant];exact one_ne_zero))) (2*j)
lemma rawExtractedCoefficient_analyticAt (P:PsiTheory)(p:ℕ)(hp:1≤p)(j:ℕ)(Y:ℝ)(hY:Y∈Ioo (0:ℝ) y₀):
    AnalyticAt ℝ (rawExtractedCoefficient P p j) Y:=by
  have hx:XR Y∈Ioo (0:ℝ) xCritical:=by
    have hmono:=XR_strictMonoOn
    constructor
    · simpa only[XR_zero] using hmono y₀_pos.le hY.2.le hY.1
    · exact hmono hY.2.le (Set.mem_Iic.mpr (le_refl y₀)) hY.2
  exact (rawExtractedCoefficient_weight_analyticAt P p hp j (XR Y) hx).comp (XR_analyticAt Y)
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma rawExtractedCoefficient_complex_germ (P:PsiTheory)(p:ℕ)(hp:1≤p)(j:ℕ)(Y:ℝ)(hY:Y∈Ioo (0:ℝ) y₀):
    ∃F:ℂ→ℂ,AnalyticAt ℂ F (Y:ℂ) ∧
      (fun t:ℝ=>F (t:ℂ))=ᶠ[𝓝 Y] (fun t:ℝ=>(WP.HigherOrder.rawExtractedCoefficient P p j t:ℂ)):=
  realAnalyticAt_complex_germ _ Y (rawExtractedCoefficient_analyticAt P p hp j Y hY)
lemma rawExtractedCoefficient_analyticOnNhd (P:PsiTheory)(p:ℕ)(hp:1≤p)(j:ℕ):
    AnalyticOnNhd ℝ (WP.HigherOrder.rawExtractedCoefficient P p j) (Ioo (0:ℝ) y₀):=
  fun Y hY=>rawExtractedCoefficient_analyticAt P p hp j Y hY
end WP.Analysis
