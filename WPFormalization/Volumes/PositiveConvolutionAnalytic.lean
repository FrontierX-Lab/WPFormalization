import WPFormalization.Volumes.PositiveConvolutionProof
/-! Actual analytic companions to Lemma 9.1. The original quotient is
holomorphic throughout the cusp disk, its Taylor coefficients are real
and nonnegative, and the universal factor itself has positive real jets.
These follow from the actual positive polynomial factorization. -/
noncomputable section
namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma convolutionR_analyticAt_disk (P:PsiTheory) (g p:ℕ) (z:ℂ) (hz:‖z‖<xCritical):
    AnalyticAt ℂ (convolutionR P g p) z:=by
  have hf:AnalyticAt ℂ (iteratedDeriv p (Phi P g)) z:=by
    simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P g z hz).iterated_deriv p
  have hv:AnalyticAt ℂ (universalV P) z:=by
    change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z
    simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 z hz).iterated_deriv 3
  exact hf.div (hv.pow _) (pow_ne_zero _ (planar_third_ne_zero P z hz))
lemma convolutionR_eq_regularized_polynomial (P:PsiTheory) (g p:ℕ) (hp:1 ≤ p) (hs:Stable g p):
    ∃F:KernelPolynomial,∀z:ℂ,‖z‖<xCritical→convolutionR P g p z=regularizedKernelPolynomial P F z:=by
  obtain ⟨F,hF⟩:=factorization_by_positive_polynomial P g p hp hs
  refine ⟨F,?_⟩
  intro z hz
  unfold convolutionR universalV
  rw[hF z hz]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (planar_third_ne_zero P z hz))
lemma convolutionR_positiveJets (P:PsiTheory) (g p:ℕ) (hp:1 ≤ p) (hs:Stable g p):
    PositiveJets (convolutionR P g p):=by
  obtain ⟨F,hF⟩:=convolutionR_eq_regularized_polynomial P g p hp hs
  have he:(convolutionR P g p)=ᶠ[𝓝 (0:ℂ)] regularizedKernelPolynomial P F:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter] with z hz
    exact hF z (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
  intro n
  obtain ⟨a,ha⟩:=(regularizedKernelPolynomial_positiveJets P F) n
  exact ⟨a,by rw[he.iteratedDeriv_eq,ha]⟩
lemma convolutionR_real_nonnegative_coefficients (P:PsiTheory) (g p:ℕ) (hp:1 ≤ p) (hs:Stable g p):
    ∀n,0 ≤ realCoeff (convolutionR P g p) n ∧ (WP.coeff (convolutionR P g p) n).im=0:=
  (convolutionR_positiveJets P g p hp hs).coefficient_nonneg
lemma universalV_positiveJets (P:PsiTheory):PositiveJets (universalV P):=by
  intro n
  have hn:0 ≤ shifted P 0 (List.replicate (n+3) 0) 0:=
    shifted_zero_nonneg_nonempty P 0 (n+3) (by omega) 0 ⟨le_rfl,y₀_pos⟩
  refine ⟨⟨_,hn⟩,?_⟩
  change iteratedDeriv n (iteratedDeriv 3 (Phi P 0)) 0=_
  rw[Analysis.iteratedDeriv_iteratedDeriv_eq,Phi_iteratedDeriv_zero]
  rfl
lemma universalV_zero (P:PsiTheory):universalV P 0=1:=by
  have hs:=planarThird_ofReal P 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩
  simpa only[Analysis.inverseY_zero_value,a_zero,inv_one,Complex.ofReal_one,Complex.ofReal_zero,universalV] using hs
end WP.PositiveConvolution
