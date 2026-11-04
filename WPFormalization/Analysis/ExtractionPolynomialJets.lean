import WPFormalization.Analysis.StationaryTaylorCoefficients
import WPFormalization.Analysis.GaussianFunctionalRealization
/-! Finite algebraic Taylor identities for the prescribed extraction polynomials, and an exact real Gaussian integral for the original extractionNumerator. No coefficient definition is changed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma extractionExpPolynomial_eval_of_jets (p:ℕ) (x:ℝ) (E:ℂ → ℂ) (w:ℂ) (n:ℕ)
    (hE:AnalyticAt ℂ E 0) (hE0:E 0=0)
    (hjets:∀i:ℕ,i ≤ n → WP.coeff E i=
      Polynomial.eval₂ Complex.ofRealHom w (HigherOrder.extractionLogPolynomial p x i)) :
    WP.coeff (fun τ:ℂ=>Complex.exp (E τ)) n=
      Polynomial.eval₂ Complex.ofRealHom w (HigherOrder.extractionExpPolynomial p x n) := by
  let ev:Polynomial ℝ →+*ℂ:=Polynomial.eval₂RingHom Complex.ofRealHom w
  let R:PowerSeries (Polynomial ℝ):=PowerSeries.mk (HigherOrder.extractionLogPolynomial p x)
  have hjet:∀i:ℕ,i ≤ n → PowerSeries.coeff i (taylor E)=PowerSeries.coeff i (PowerSeries.map ev R) := by
    intro i hi
    simpa only [taylor_coeff,PowerSeries.coeff_map,PowerSeries.coeff_mk,R,ev,
      Polynomial.coe_eval₂RingHom] using hjets i hi
  rw [taylor_exp_coeff_finite E hE hE0 n]
  change (∑j ∈ Finset.range (n+1),PowerSeries.coeff n ((taylor E)^j)/(j.factorial:ℂ))=
    ev (HigherOrder.extractionExpPolynomial p x n)
  change (∑j ∈ Finset.range (n+1),PowerSeries.coeff n ((taylor E)^j)/(j.factorial:ℂ))=
    ev (∑j ∈ Finset.range (n+1),Polynomial.C ((j.factorial:ℝ)⁻¹)*PowerSeries.coeff n (R^j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_pow_eq_of_coeff_eq (taylor E) (PowerSeries.map ev R) n hjet j n le_rfl,
    ←map_pow,PowerSeries.coeff_map,map_mul]
  have hc:ev (Polynomial.C ((j.factorial:ℝ)⁻¹))=(j.factorial:ℂ)⁻¹ := by simp [ev]
  rw [hc]
  ring

def extractionNumeratorPolynomial (P:WP.PsiTheory) (p:ℕ) (x:ℝ) (n:ℕ):Polynomial ℝ :=
  ∑j ∈ Finset.range (n+1),HigherOrder.extractionExpPolynomial p x j*
    HigherOrder.markedTaylorPolynomial P p x (n-j)
lemma extractionNumerator_gaussian_integral (P:WP.PsiTheory) (p:ℕ) (x:ℝ) (n:ℕ) :
    (∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) •
      ((extractionNumeratorPolynomial P p x n).map Complex.ofRealHom).eval (Complex.I*(w:ℂ)))=
      (Real.sqrt (2*Real.pi):ℂ)*((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ) := by
  simpa only [HigherOrder.extractionNumerator,PowerSeries.coeff_mk,extractionNumeratorPolynomial] using
    gaussianFunctional_integral_realization (extractionNumeratorPolynomial P p x n)
end WP.Analysis
