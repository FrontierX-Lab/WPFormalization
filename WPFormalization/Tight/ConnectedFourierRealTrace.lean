import WPFormalization.Tight.ConnectedFourierDomination
/-! Exact real-axis trace of a centered tight generating function. -/
noncomputable section
namespace WP.TightConnected
open Set TightMoments
lemma centeredTightGenerating_ofReal (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (x μ σ u:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (htu:x*Real.exp (u/σ)∈Ico (0:ℝ) xCritical):
    centeredTightGenerating P g p L x μ σ (u:ℂ)=
      ((Real.exp (-μ*u/σ)*tightShiftedPolynomial P g p
        (inverseY (x*Real.exp (u/σ))) L/tightShiftedPolynomial P g p (inverseY x) L:ℝ):ℂ) := by
  have harg:(x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ))=((x*Real.exp (u/σ):ℝ):ℂ) := by
    rw [←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
  have hex:Complex.exp (-(μ:ℂ)*(u:ℂ)/(σ:ℂ))=(Real.exp (-μ*u/σ):ℂ) := by
    rw [←Complex.ofReal_neg,←Complex.ofReal_mul,←Complex.ofReal_div,←Complex.ofReal_exp]
  unfold centeredTightGenerating
  rw [harg,hex,momentTightG_ofReal P g p L _ htu,momentTightG_ofReal P g p L x hx]
  push_cast
  ring
end WP.TightConnected
