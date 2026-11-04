import WPFormalization.Tight.ComplexMoments
import WPFormalization.Tight.PositiveConvolution
/-! The canonical analytic continuation of the finite shifted polynomial,
including the unmarked case. Its protected-tight geometric realization is
separate. For positive protected count its factor has positive coefficients. -/
noncomputable section
namespace WP.TightMoments
open Set Filter PositiveConvolution
open scoped Topology

def scaledPlaneMoments (P:PsiTheory) (j:ℕ) (z:ℂ):ℂ:=
  (2*Real.pi^2:ℝ)^j*iteratedDeriv (j+1) X (planarInverse P z)
def momentTightG (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ) (z:ℂ):ℂ:=
  complexMomentPolynomial P g p (fun j=>scaledPlaneMoments P j z) L/
    (2*Real.pi^2:ℝ)^(dimension g p)
lemma scaledPlaneMoments_analyticAt (P:PsiTheory) (j:ℕ) (z:ℂ) (hz:‖z‖<xCritical):
    AnalyticAt ℂ (scaledPlaneMoments P j) z:=by
  exact analyticAt_const.mul (((iteratedDeriv_X_differentiable (j+1)).analyticAt _).comp
    (planarInverse_analyticAt P z hz))
lemma scaledPlaneMoments_zero_index (P:PsiTheory) (z:ℂ):
    scaledPlaneMoments P 0 z=deriv X (planarInverse P z):=by
  simp only [scaledPlaneMoments,pow_zero,one_mul,zero_add,iteratedDeriv_one]
lemma momentTightG_analyticAt (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (z:ℂ) (hz:‖z‖<xCritical):AnalyticAt ℂ (momentTightG P g p L) z:=by
  apply AnalyticAt.div_const
  apply complexMomentPolynomial_analyticAt
  · exact fun j=>scaledPlaneMoments_analyticAt P j z hz
  · rw [scaledPlaneMoments_zero_index]
    exact derivX_planarInverse_ne_zero P z hz
lemma scaledPlaneMoments_ofReal (P:PsiTheory) (j:ℕ) (x:ℝ)
    (hx:x∈Ico (0:ℝ) xCritical):
    scaledPlaneMoments P j (x:ℂ)=((2*Real.pi^2)^j*planeMoments (inverseY x) j:ℝ):=by
  unfold scaledPlaneMoments
  rw [planarInverse_ofReal P x hx]
  have hm:iteratedDeriv (j+1) X (inverseY x:ℂ)=(planeMoments (inverseY x) j:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using iteratedDeriv_X_im_ofReal (j+1) (inverseY x)
  rw [hm]
  push_cast
  rfl
lemma momentTightG_ofReal (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    momentTightG P g p L (x:ℂ)=(tightShiftedPolynomial P g p (inverseY x) L:ℂ):=by
  unfold momentTightG
  simp_rw [scaledPlaneMoments_ofReal P _ x hx]
  rw [complexMomentPolynomial_ofReal]
  have he:=momentPolynomial_scale_to_shifted P g p (inverseY x) L
  exact_mod_cast he
lemma momentTightG_taylor (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (z:ℂ) (hz:‖z‖<xCritical):
    HasSum (fun j=>WP.coeff (momentTightG P g p L) j*z^j) (momentTightG P g p L z):=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (momentTightG_analyticAt P g p L) z hz

lemma momentTightG_eq_positive_factor (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (z:ℂ) (hz:‖z‖<xCritical):
    momentTightG P g p L z=universalV P z^(complexity g p)*TightConvolution.tightR P g p L z:=by
  have hf:AnalyticOnNhd ℂ (momentTightG P g p L) (Metric.ball 0 xCritical):=by
    intro w hw
    exact momentTightG_analyticAt P g p L w (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hq:AnalyticOnNhd ℂ (TightConvolution.tightG P g p L) (Metric.ball 0 xCritical):=by
    intro w hw
    exact TightConvolution.tightG_analyticAt P g p L w
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hc:xCritical/2∈Ioo (0:ℝ) xCritical:=⟨half_pos Analysis.xCritical_pos_parameter,
    half_lt_self Analysis.xCritical_pos_parameter⟩
  have hmem:((xCritical/2:ℝ):ℂ)∈Metric.ball 0 xCritical:=by
    simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hc.1.le] using hc.2
  have he:EqOn (momentTightG P g p L) (TightConvolution.tightG P g p L) (Metric.ball 0 xCritical):=by
    apply Analysis.complex_identity_of_real_germ _ _ _ (xCritical/2) hf hq
      (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx
    rw [momentTightG_ofReal P g p L x ⟨hx.1.le,hx.2⟩,
      TightConvolution.tightG_ofReal P g p hp hs L x ⟨hx.1.le,hx.2⟩]
  exact he (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
end WP.TightMoments
