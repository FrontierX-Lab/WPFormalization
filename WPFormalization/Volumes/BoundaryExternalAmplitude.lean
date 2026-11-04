import WPFormalization.Volumes.PositiveConvolutionAnalytic

/-! Positive holomorphic continuation of every actual external amplitude.
The finite kernel polynomial is chosen from its proved representation;
non-admissible degrees vanish by the original definition of shifted. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

def externalPolynomial (P : PsiTheory) (g : ℕ) (d : List ℕ) : KernelPolynomial :=
  if h : 1 ≤ d.length ∧ Stable g d.length ∧ d.sum ≤ dimension g d.length then
    Classical.choose (exists_regularized_amplitude_polynomial P g d h.1 h.2.1 h.2.2)
  else 0

lemma externalPolynomial_spec (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hn : 1 ≤ d.length) (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length) :
    ∀ Y ∈ Ico (0:ℝ) y₀, a Y^(complexity g d.length)*shifted P g d Y =
      evalKernel (fun l => (Analysis.kInverseCoeff l Y).re) (externalPolynomial P g d) := by
  rw [externalPolynomial,dif_pos ⟨hn,hs,hd⟩]
  exact (Classical.choose_spec
    (exists_regularized_amplitude_polynomial P g d hn hs hd)).2

def externalAmplitude (P : PsiTheory) (g : ℕ) (d : List ℕ) (z : ℂ) : ℂ :=
  regularizedKernelPolynomial P (externalPolynomial P g d) z

lemma externalAmplitude_analyticAt (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (z : ℂ) (hz : ‖z‖ < xCritical) : AnalyticAt ℂ (externalAmplitude P g d) z :=
  regularizedKernelPolynomial_analyticAt P _ z hz

lemma externalAmplitude_positiveJets (P : PsiTheory) (g : ℕ) (d : List ℕ) :
    PositiveJets (externalAmplitude P g d) :=
  regularizedKernelPolynomial_positiveJets P _

lemma externalAmplitude_ofReal (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hn : 1 ≤ d.length) (hs : Stable g d.length)
    (x : ℝ) (hx : x ∈ Ico (0:ℝ) xCritical) :
    externalAmplitude P g d (x:ℂ) =
      Complex.ofReal (a (inverseY x)^(complexity g d.length)*shifted P g d (inverseY x)) := by
  have hy := (inverseY_branch x hx).1
  by_cases hd : d.sum ≤ dimension g d.length
  · unfold externalAmplitude regularizedKernelPolynomial
    rw [planarInverse_ofReal P x hx]
    have he : (fun l => Analysis.kInverseCoeff l (Complex.ofReal (inverseY x))) =
        (fun l => Complex.ofReal (Analysis.kInverseCoeff l (Complex.ofReal (inverseY x))).re) := by
      funext l
      exact kernel_inverse_ofReal l (inverseY x) hy
    rw [he,polynomial_eval_ofReal]
    exact congrArg Complex.ofReal (externalPolynomial_spec P g d hn hs hd _ hy).symm
  · have hz : shifted P g d (inverseY x) = 0 := by simp [shifted,hd]
    simp only [externalAmplitude,externalPolynomial,dif_neg (by tauto :
      ¬(1 ≤ d.length ∧ Stable g d.length ∧ d.sum ≤ dimension g d.length)),
      regularizedKernelPolynomial,MvPolynomial.eval₂_zero,hz,mul_zero,Complex.ofReal_zero]

lemma externalAmplitude_real_nonnegative_coefficients (P : PsiTheory) (g : ℕ) (d : List ℕ) :
    ∀ j, 0 ≤ realCoeff (externalAmplitude P g d) j ∧
      (WP.coeff (externalAmplitude P g d) j).im = 0 :=
  (externalAmplitude_positiveJets P g d).coefficient_nonneg

lemma externalAmplitude_taylor (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (z : ℂ) (hz : ‖z‖ < xCritical) :
    HasSum (fun j => WP.coeff (externalAmplitude P g d) j*z^j)
      (externalAmplitude P g d z) :=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (externalAmplitude_analyticAt P g d) z hz

end WP.BoundaryConvolution
