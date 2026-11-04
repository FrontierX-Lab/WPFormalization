import WPFormalization.Tight.ConnectedFourierInversion
import WPFormalization.Tight.GeometricGeneratingFunctions
/-! The Fourier masses are genuine probabilities of the actual geometric
tight generating function, through the proved cusp coefficient identity. -/
noncomputable section
namespace WP.TightConnected
open Set TightMoments External
lemma tightMass_eq_geometric {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (B:BuddZonneveldTransform G T)
    (g p:ℕ) (hs:Stable g p) (L:Fin p→ℝ) (hL:∀i,0≤L i)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical) (k:ℕ):
    tightMass P g p L k x=
      (tightVolume T g p k L (fun _=>0)/
        ((2*Real.pi^2)^(dimension g p+k)*(k.factorial:ℝ)))*x^k/
        tightGeneratingFunction T g p L x := by
  have he:tightGeneratingFunction T g p L x=tightShiftedPolynomial P g p (inverseY x) L :=
    (tightGeneratingFunction_hasSum T B g p hs L hL x hx).tsum_eq
  unfold tightMass
  rw [←geometric_tight_cusp_coefficient T B g p hs L hL k,
    momentTightG_ofReal P g p L x hx,Complex.ofReal_re,he]
lemma tightMass_nonnegative (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical) (k:ℕ):
    0≤tightMass P g p L k x := by
  unfold tightMass
  exact div_nonneg (mul_nonneg
    (momentTightG_real_nonnegative_coefficients P g p hp hs L k).1 (pow_nonneg hx.1 k))
    (momentTightG_real_pos P g p hp hs L x hx).le
lemma tightMass_hasSum (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    HasSum (fun k=>tightMass P g p L k x) 1 := by
  have hn:‖(x:ℂ)‖<xCritical := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have ht:=Complex.reCLM.hasSum (momentTightG_taylor P g p L (x:ℂ) hn)
  have ht':HasSum (fun k=>realCoeff (momentTightG P g p L) k*x^k)
      (momentTightG P g p L (x:ℂ)).re := by
    convert ht using 1
    · ext k
      simp only [Complex.reCLM_apply,←Complex.ofReal_pow,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]
    · rfl
  have he:=ht'.div_const (momentTightG P g p L (x:ℂ)).re
  simpa only [tightMass,div_self (momentTightG_real_pos P g p hp hs L x hx).ne'] using he
end WP.TightConnected
