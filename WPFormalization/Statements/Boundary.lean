import WPFormalization.Volumes.BoundaryProof
import WPFormalization.Volumes.DiagonalChainProof
import WPFormalization.Statements.ChainDefinitions
import WPFormalization.Volumes.BoundaryPolynomial
import WPFormalization.Statements.BoundaryDefinitions
import WPFormalization.Statements.Coefficients
import WPFormalization.Statements.ConvolutionDefinitions
import WPFormalization.Volumes.PositiveConvolutionProof
import WPFormalization.Volumes.PointMassProof

/-! Boundary-volume polynomials and diagonal rates in the constrained numerical model. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Proposition 9.4: the additional zero boundary lengths and fixed p are explicit. -/
/- Blueprint label(s): prop:bounded-boundaries
Paper v3: 9.4 [PDF 44]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "prop:bounded-boundaries"]
theorem bounded_boundaries (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) (L₀ : ℝ) (hL : 0 ≤ L₀) :
    ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ n : ℕ, p ≤ n →
      ∀ L : Fin n → ℝ, (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L₀) →
      (∀ i, p ≤ i.val → L i = 0) →
        |boundaryVolumeModel P g n L /
          (volumeModel P g n * ∏ i : Fin n,
            boundaryFactor (densityY ((n : ℝ)/g)) (L i))-1| ≤ ε := by
  exact bounded_boundaries_proof P p hp L₀ hL

/- Lemma 9.1. Taylor convergence is included, not inferred from coefficient signs. -/
/- Blueprint label(s): lem:convolution
Paper v3: 9.1 [PDF 40]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:convolution"]
theorem positive_convolution (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hst : Stable g p) :
    (∀ x ∈ Set.Ico 0 xCritical, universalV P x = ((a (inverseY x))⁻¹ : ℝ) ∧
      iteratedDeriv p (Phi P g) x =
        universalV P x^(complexity g p)*convolutionR P g p x) ∧
    (∀ j, 0 ≤ realCoeff (convolutionR P g p) j) ∧
    (∀ z : ℂ, ‖z‖ < xCritical →
      HasSum (fun j => coeff (convolutionR P g p) j*z^j) (convolutionR P g p z)) := by
  exact positive_convolution_proof P g p hp hst

/- Lemma 9.3, arbitrary analytic nonnegative convolution remainder, not a model assumption. -/
/- Blueprint label(s): lem:point-mass
Paper v3: 9.3 [PDF 43]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:point-mass"]
theorem point_mass_bound (P : PsiTheory) (c₀ : ℝ) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ h h' : ℕ, 1 ≤ h → 16 ≤ h' → c₀*h ≤ h' →
    ∀ x ∈ Set.Ioo 0 xCritical, ∀ R : ℂ → ℂ,
      AnalyticOnNhd ℂ R (Metric.ball 0 xCritical) →
      (∀ j, 0 ≤ realCoeff R j ∧ (coeff R j).im = 0) → 0 < (R x).re → (R x).im = 0 →
      (∀ z : ℂ, ‖z‖ < xCritical → HasSum (fun j => coeff R j*z^j) (R z)) →
      ∀ j : ℕ,
        realCoeff (fun z => universalV P z^h'*R z) j*x^j /
          (universalV P x^h'*R x).re ≤ C/Real.sqrt (h*euler Psi x) := by
  exact point_mass_bound_proof P c₀ hc

/- Theorem 1.5. The first limit includes bounded genera and genus zero. -/
/- Blueprint label(s): thm:chain
Paper v3: 1.5 [PDF 8]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "thm:chain"]
theorem diagonal_chain (P : PsiTheory) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g n : ℕ, Stable g n → N ≤ 2*g+n →
      |Real.log (normalizedVolume P g n) - ((2*(g : ℝ)+n)/2)*
        chainProfile ((n : ℝ)/(2*g+n))| ≤ ε*(2*g+n)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ G₀ : ℕ, ∀ G ≥ G₀, 2 ≤ G → ∀ j : ℕ, j ≤ G →
      |Real.log (volumeModel P (G-j) (2*j)/volumeModel P G 0)/G-
        chainProfile ((j : ℝ)/G)| ≤ ε) := by
  exact diagonal_chain_proof P
end WP
