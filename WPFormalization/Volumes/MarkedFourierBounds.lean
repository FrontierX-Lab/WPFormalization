import WPFormalization.Volumes.MarkedGeneratingPositivity
import WPFormalization.Volumes.PointMassCompact

/-! Actual marked Fourier ratios are dominated by the positive planar factor.
The compact Gaussian point bound follows from its proved zero and one
coefficients. No local-limit or tail conclusion is assumed. -/

namespace WP
open Set
lemma convolutionR_positive_real (P:PsiTheory) (g p:ℕ) (hp:1≤p)
    (hs:Stable g p) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    0<(convolutionR P g p x).re ∧ (convolutionR P g p x).im=0:=by
  have he:=PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs x hx
  have hv:=PositiveConvolution.planarThird_ofReal P x hx
  change universalV P x=(((a (inverseY x))⁻¹:ℝ):ℂ) at hv
  have hb:=inverseY_branch x hx
  have hU:=shifted_zero_pos_nonempty P g p hp hs (inverseY x) hb.1
  have ha:=a_pos _ hb.1
  rw[convolutionR,he,hv,←Complex.ofReal_pow,←Complex.ofReal_div,Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨div_pos hU (pow_pos (inv_pos.mpr ha) _),rfl⟩

lemma marked_generating_circle_domination (P:PsiTheory) (g p:ℕ) (hp:1≤p)
    (hs:Stable g p) (x:ℝ) (hx:x∈Ioo (0:ℝ) xCritical) (z:ℂ) (hz:‖z‖=x):
    ‖iteratedDeriv p (Phi P g) z/iteratedDeriv p (Phi P g) (x:ℂ)‖≤
      ‖universalV P z/universalV P (x:ℂ)‖^(complexity g p):=by
  have hxi:x∈Ico (0:ℝ) xCritical:=⟨hx.1.le,hx.2⟩
  have hvr:=PositiveConvolution.universalV_positive_real P x hxi
  have hrr:=convolutionR_positive_real P g p hp hs x hxi
  have hco:=PositiveConvolution.positive_series_circle_domination (universalV P) (convolutionR P g p)
    x (complexity g p) hx.1.le hvr.1 hvr.2 hrr.1 hrr.2
    (PositiveConvolution.convolutionR_real_nonnegative_coefficients P g p hp hs)
    (fun w hw=>PositiveConvolution.analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
      (fun z hz=>PositiveConvolution.convolutionR_analyticAt_disk P g p z hz) w (hw.trans_lt hx.2)) z hz.le
  have hf(w:ℂ)(hw:‖w‖<xCritical):
      universalV P w^(complexity g p)*convolutionR P g p w=iteratedDeriv p (Phi P g) w:=by
    unfold convolutionR
    exact mul_div_cancel₀ _ (pow_ne_zero _ (PositiveConvolution.planar_third_ne_zero P w hw))
  rw[hf z (hz.trans_lt hx.2),hf (x:ℂ) (by rw[Complex.norm_of_nonneg hx.1.le];exact hx.2)] at hco
  rw[norm_div,marked_generating_norm_real P g p hp hs x hxi]
  exact hco

lemma marked_generating_gaussian_point_bound (P:PsiTheory) (g p:ℕ) (hp:1≤p)
    (hs:Stable g p) (x B:ℝ) (hx:x∈Ioo (0:ℝ) xCritical) (hB:0<B)
    (hVB:(universalV P x).re≤B) (θ:ℝ) (hθ:|θ|≤Real.pi):
    ‖iteratedDeriv p (Phi P g) ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/
      iteratedDeriv p (Phi P g) (x:ℂ)‖≤
        Real.exp (-((2/(B^2*Real.pi^2))*(complexity g p:ℝ)*x)*θ^2):=by
  have hz:‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖=x:=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
  exact (marked_generating_circle_domination P g p hp hs x hx _ hz).trans
    (PositiveConvolution.universalV_gaussian_point_bound P x B hx hB hVB θ hθ (complexity g p))
end WP
