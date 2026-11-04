import WPFormalization.Tight.ShiftedPolynomial
import WPFormalization.Volumes.BoundaryExternalAmplitude
/-! Positive analytic factor of the actual finite shifted-insertion polynomial.
The geometric tight-volume realization remains separate. -/
noncomputable section
namespace WP
open Set Filter
open scoped Topology
namespace TightConvolution
open BoundaryConvolution PositiveConvolution

def lengthWeight (p:ℕ) (L:Fin p→ℝ) (d:Fin p→ℕ):ℝ:=
  ∏i,L i^(2*d i)/((2*Real.pi^2)^(d i)*(2*d i+1).factorial)
lemma lengthWeight_nonneg (p:ℕ) (L:Fin p→ℝ) (d:Fin p→ℕ):0≤lengthWeight p L d:=by
  apply Finset.prod_nonneg
  intro i hi
  apply div_nonneg
  · simpa only [←pow_mul] using pow_nonneg (sq_nonneg (L i)) (d i)
  · positivity

def tightR (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ) (z:ℂ):ℂ:=
  ∑d∈degreeTuples g p,externalAmplitude P g (List.ofFn d) z*(lengthWeight p L d:ℂ)
def tightG (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ) (z:ℂ):ℂ:=
  universalV P z^(complexity g p)*tightR P g p L z

lemma tightR_analyticAt (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (z:ℂ) (hz:‖z‖<xCritical):AnalyticAt ℂ (tightR P g p L) z:=by
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact (externalAmplitude_analyticAt P g _ z hz).mul analyticAt_const
lemma tightR_positiveJets (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ):
    PositiveJets (tightR P g p L):=by
  have hx:‖(0:ℂ)‖<xCritical:=by simpa using Analysis.xCritical_pos_parameter
  apply PositiveJets.sum
  · intro d hd
    exact (externalAmplitude_analyticAt P g _ 0 hx).mul analyticAt_const
  · intro d hd
    have hc:PositiveJets (fun _:ℂ=>(lengthWeight p L d:ℂ)):=by
      exact PositiveJets.const ⟨lengthWeight p L d,lengthWeight_nonneg p L d⟩
    exact PositiveJets.mul (externalAmplitude_analyticAt P g _ 0 hx) analyticAt_const
      (externalAmplitude_positiveJets P g _) hc
lemma tightR_real_nonnegative_coefficients (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ):
    ∀j,0≤realCoeff (tightR P g p L) j ∧ (WP.coeff (tightR P g p L) j).im=0:=
  (tightR_positiveJets P g p L).coefficient_nonneg
lemma tightR_taylor (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (z:ℂ) (hz:‖z‖<xCritical):
    HasSum (fun j=>WP.coeff (tightR P g p L) j*z^j) (tightR P g p L z):=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (tightR_analyticAt P g p L) z hz
lemma tightG_analyticAt (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (z:ℂ) (hz:‖z‖<xCritical):AnalyticAt ℂ (tightG P g p L) z:=by
  apply AnalyticAt.mul _ (tightR_analyticAt P g p L z hz)
  have hv:AnalyticAt ℂ (universalV P) z:=by
    change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z
    simpa only [iteratedDeriv_eq_iterate] using
      (Phi_analyticAt_open_disk P 0 z hz).iterated_deriv 3
  exact hv.pow _
lemma tightG_positiveJets (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ):
    PositiveJets (tightG P g p L):=by
  have hx:‖(0:ℂ)‖<xCritical:=by simpa using Analysis.xCritical_pos_parameter
  have hv:AnalyticAt ℂ (universalV P) 0:=by
    change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) 0
    simpa only [iteratedDeriv_eq_iterate] using
      (Phi_analyticAt_open_disk P 0 0 hx).iterated_deriv 3
  exact PositiveJets.mul (hv.pow _) (tightR_analyticAt P g p L 0 hx)
    (PositiveJets.pow hv (universalV_positiveJets P) _) (tightR_positiveJets P g p L)
lemma tightG_taylor (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (z:ℂ) (hz:‖z‖<xCritical):
    HasSum (fun j=>WP.coeff (tightG P g p L) j*z^j) (tightG P g p L z):=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (tightG_analyticAt P g p L) z hz

lemma tightR_ofReal (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    tightR P g p L (x:ℂ)=
      (a (inverseY x)^(complexity g p)*tightShiftedPolynomial P g p (inverseY x) L:ℝ):=by
  unfold tightR
  have htrace(d:Fin p→ℕ):externalAmplitude P g (List.ofFn d) (x:ℂ)=
      (a (inverseY x)^(complexity g p)*shifted P g (List.ofFn d) (inverseY x):ℝ):=by
    simpa only [List.length_ofFn] using externalAmplitude_ofReal P g (List.ofFn d)
      (by simpa only [List.length_ofFn] using hp)
      (by simpa only [List.length_ofFn] using hs) x hx
  simp_rw [htrace]
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum]
  congr 1
  unfold tightShiftedPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change (_*_)*_= _*(_*_)
  unfold lengthWeight
  ring
lemma tightG_ofReal (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    tightG P g p L (x:ℂ)=(tightShiftedPolynomial P g p (inverseY x) L:ℂ):=by
  have ha:= (a_pos (inverseY x) (inverseY_branch x hx).1).ne'
  unfold tightG
  rw [show universalV P (x:ℂ)=((a (inverseY x))⁻¹:ℂ) by simpa only [universalV,Complex.ofReal_inv] using planarThird_ofReal P x hx,
    tightR_ofReal P g p hp hs L x hx]
  push_cast
  simp only [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ha)),one_mul]
end TightConvolution

end WP
