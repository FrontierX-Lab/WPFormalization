import WPFormalization.Volumes.BoundaryTranslationKernel
import WPFormalization.Volumes.BoundaryExternalAmplitude
import WPFormalization.Statements.BoundaryDefinitions

/-! An explicit finite positive convolution for the full boundary insertion.
The infinite translation sum is an actual entire X derivative. No boundary
asymptotic or generating-function identification is assumed here. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

def lengthTime (L : ℝ) : ℝ := L^2/(4*Real.pi^2)
lemma lengthTime_nonneg (L : ℝ) : 0 ≤ lengthTime L := by unfold lengthTime; positivity

def boundaryR (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ) (z : ℂ) : ℂ :=
  ∑ b ∈ degreeTuples g p,
    externalAmplitude P g (List.ofFn b) z *
      ∏ i, ((oddFactorial (b i):ℂ))⁻¹ *
        translationWeight (lengthTime (L i)) (b i) (planarInverse P z)

def boundaryG (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ) (z : ℂ) : ℂ :=
  universalV P z^(complexity g p)*boundaryR P g p L z

lemma boundaryR_analyticAt (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (z : ℂ) (hz : ‖z‖ < xCritical) : AnalyticAt ℂ (boundaryR P g p L) z := by
  apply Finset.analyticAt_fun_sum
  intro b hb
  apply AnalyticAt.mul (externalAmplitude_analyticAt P g _ z hz)
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact analyticAt_const.mul
    ((translationWeight_analyticAt _ _ _).comp (planarInverse_analyticAt P z hz))

lemma boundaryR_positiveJets (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ) :
    PositiveJets (boundaryR P g p L) := by
  have hx : ‖(0:ℂ)‖ < xCritical := by simpa using Analysis.xCritical_pos_parameter
  apply PositiveJets.sum
  · intro b hb
    apply AnalyticAt.mul (externalAmplitude_analyticAt P g _ 0 hx)
    apply Finset.analyticAt_fun_prod
    intro i hi
    exact analyticAt_const.mul
      ((translationWeight_analyticAt _ _ _).comp (planarInverse_analyticAt P 0 hx))
  · intro b hb
    apply PositiveJets.mul (externalAmplitude_analyticAt P g _ 0 hx)
    · apply Finset.analyticAt_fun_prod
      intro i hi
      exact analyticAt_const.mul
        ((translationWeight_analyticAt _ _ _).comp (planarInverse_analyticAt P 0 hx))
    · exact externalAmplitude_positiveJets P g _
    · apply PositiveJets.prod
      · intro i hi
        exact analyticAt_const.mul
          ((translationWeight_analyticAt _ _ _).comp (planarInverse_analyticAt P 0 hx))
      · intro i hi
        have hconst : PositiveJets (fun _ : ℂ => (oddFactorial (b i):ℂ)⁻¹) := by
          simpa only [map_inv₀,map_natCast] using
            PositiveJets.const (((oddFactorial (b i):NNReal))⁻¹)
        apply PositiveJets.mul analyticAt_const
          ((translationWeight_analyticAt _ _ _).comp (planarInverse_analyticAt P 0 hx)) hconst
        apply PositiveJets.comp (f := translationWeight (lengthTime (L i)) (b i))
          (g := planarInverse P)
        · exact translationWeight_analyticAt _ _ 0
        · exact planarInverse_analyticAt P 0 hx
        · exact planarInverse_zero P
        · exact translationWeight_positiveJets _ (lengthTime_nonneg _) _
        · exact planarInverse_positiveJets P

lemma boundaryR_real_nonnegative_coefficients (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ) :
    ∀ j, 0 ≤ realCoeff (boundaryR P g p L) j ∧
      (WP.coeff (boundaryR P g p L) j).im=0 :=
  (boundaryR_positiveJets P g p L).coefficient_nonneg

lemma boundaryR_taylor (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (z : ℂ) (hz : ‖z‖ < xCritical) :
    HasSum (fun j => WP.coeff (boundaryR P g p L) j*z^j) (boundaryR P g p L z) :=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (boundaryR_analyticAt P g p L) z hz

lemma boundaryG_analyticAt (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (z : ℂ) (hz : ‖z‖ < xCritical) : AnalyticAt ℂ (boundaryG P g p L) z := by
  apply AnalyticAt.mul _ (boundaryR_analyticAt P g p L z hz)
  have hv : AnalyticAt ℂ (universalV P) z := by
    change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z
    simpa only [iteratedDeriv_eq_iterate] using
      (Phi_analyticAt_open_disk P 0 z hz).iterated_deriv 3
  convert! hv.pow (complexity g p) using 1

lemma boundaryG_positiveJets (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ) :
    PositiveJets (boundaryG P g p L) := by
  have hx : ‖(0:ℂ)‖ < xCritical := by simpa using Analysis.xCritical_pos_parameter
  have hv : AnalyticAt ℂ (universalV P) 0 := by
    change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) 0
    simpa only [iteratedDeriv_eq_iterate] using
      (Phi_analyticAt_open_disk P 0 0 hx).iterated_deriv 3
  exact PositiveJets.mul (hv.pow _) (boundaryR_analyticAt P g p L 0 hx)
    (PositiveJets.pow hv (universalV_positiveJets P) _) (boundaryR_positiveJets P g p L)

end WP.BoundaryConvolution
