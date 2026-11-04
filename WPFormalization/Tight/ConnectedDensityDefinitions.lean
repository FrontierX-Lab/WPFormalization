import WPFormalization.Tight.GeneratingFunctions
import WPFormalization.Statements.Intensities
noncomputable section
namespace WP.TightConnected
/-- Genuine connected-cut coefficient ratio on the paper's density scale.
The numerator keeps its protected physical lengths fixed when evaluated. -/
def connectedDensityCoefficientRatio (P:PsiTheory) (k g n:ℕ) (t:Fin (2*k)→ℝ) : ℝ :=
  realCoeff (TightMoments.momentTightG P (g-k) (2*k)
    (fun i=>t i/tightScale ((n:ℝ)/(g:ℝ)))) n /
    (realCoeff (Phi P g) n *
      ((4*r (densityY ((n:ℝ)/(g:ℝ))))^k*∏i,boundaryFactor 0 (t i)))
end WP.TightConnected
