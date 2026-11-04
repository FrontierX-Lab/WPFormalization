import WPFormalization.Tight.GeneratingFunctions
import WPFormalization.Volumes.PointMassFourier
import WPFormalization.Analysis.SlitDiskComparison
/-! Positive-series Fourier control for the actual tight generating function.
The physical length vector is fixed throughout each complex variation. -/
noncomputable section
namespace WP.TightConnected
open Set Filter PositiveConvolution TightMoments
open scoped Topology
lemma momentTightG_eq_tightG_germ (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ):momentTightG P g p L =ᶠ[𝓝 0] TightConvolution.tightG P g p L := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter] with z hz
  exact momentTightG_eq_positive_factor P g p hp hs L z
    (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
lemma momentTightG_positiveJets (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ):PositiveJets (momentTightG P g p L) := by
  intro n
  obtain ⟨a,ha⟩:=TightConvolution.tightG_positiveJets P g p L n
  exact ⟨a,(momentTightG_eq_tightG_germ P g p hp hs L).iteratedDeriv_eq n |>.trans ha⟩
lemma momentTightG_real_nonnegative_coefficients (P:PsiTheory) (g p:ℕ)
    (hp:1≤p) (hs:Stable g p) (L:Fin p→ℝ):
    ∀j,0≤realCoeff (momentTightG P g p L) j ∧ (WP.coeff (momentTightG P g p L) j).im=0 :=
  (momentTightG_positiveJets P g p hp hs L).coefficient_nonneg
lemma momentTightG_ofReal_im_zero (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):(momentTightG P g p L (x:ℂ)).im=0 := by
  rw [momentTightG_ofReal P g p L x hx,Complex.ofReal_im]
lemma tightShiftedPolynomial_pos (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀):0<tightShiftedPolynomial P g p Y L := by
  have hU:=shifted_zero_pos_nonempty P g p hp hs Y hY
  have hb:shifted P g (List.replicate p 0) Y≤tightShiftedPolynomial P g p Y L := by
    simpa only [one_mul] using
      (le_div_iff₀ hU).mp (tightShiftedPolynomial_bounds P g p hp hs Y hY L).1
  exact hU.trans_le hb
lemma momentTightG_real_pos (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    0<(momentTightG P g p L (x:ℂ)).re := by
  rw [momentTightG_ofReal P g p L x hx,Complex.ofReal_re]
  exact tightShiftedPolynomial_pos P g p hp hs L _ (inverseY_branch x hx).1
lemma tightR_real_pos (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    0<(TightConvolution.tightR P g p L (x:ℂ)).re := by
  rw [TightConvolution.tightR_ofReal P g p hp hs L x hx,Complex.ofReal_re]
  exact mul_pos (pow_pos (a_pos _ (inverseY_branch x hx).1) _)
    (tightShiftedPolynomial_pos P g p hp hs L _ (inverseY_branch x hx).1)
lemma momentTightG_circle_domination (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (L:Fin p→ℝ) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical) (z:ℂ) (hz:‖z‖≤x):
    ‖momentTightG P g p L z‖/(momentTightG P g p L (x:ℂ)).re≤
      ‖universalV P z/universalV P (x:ℂ)‖^(complexity g p) := by
  have hV:universalV P (x:ℂ)=Complex.ofReal ((a (inverseY x))⁻¹) :=
    planarThird_ofReal P x hx
  have hVp:0<(universalV P (x:ℂ)).re := by
    rw [hV,Complex.ofReal_re]
    exact inv_pos.mpr (a_pos _ (inverseY_branch x hx).1)
  have hVi:(universalV P (x:ℂ)).im=0 := by rw [hV,Complex.ofReal_im]
  have hRi:(TightConvolution.tightR P g p L (x:ℂ)).im=0 := by
    rw [TightConvolution.tightR_ofReal P g p hp hs L x hx,Complex.ofReal_im]
  rw [momentTightG_eq_positive_factor P g p hp hs L z (hz.trans_lt hx.2),
    momentTightG_eq_positive_factor P g p hp hs L (x:ℂ)
      (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)]
  exact positive_series_circle_domination (universalV P) (TightConvolution.tightR P g p L) x
    (complexity g p) hx.1 hVp hVi (tightR_real_pos P g p hp hs L x hx) hRi
    (TightConvolution.tightR_real_nonnegative_coefficients P g p L)
    (fun z hz=>TightConvolution.tightR_taylor P g p L z (hz.trans_lt hx.2)) z hz

def centeredTightGenerating (P:PsiTheory) (g p:ℕ) (L:Fin p→ℝ)
    (x μ σ:ℝ) (w:ℂ):ℂ :=
  Complex.exp (-(μ:ℂ)*w/(σ:ℂ))*
    (momentTightG P g p L ((x:ℂ)*Complex.exp (w/(σ:ℂ)))/momentTightG P g p L (x:ℂ))
lemma momentTightG_disk_domination (P : PsiTheory) (g p : ℕ) (hp : 1≤p) (hs : Stable g p) (L : Fin p → ℝ)
    (x : ℝ) (hx : x ∈ Ico 0 xCritical) (z : ℂ) (hz : ‖z‖ ≤ x) :
    ‖momentTightG P g p L z‖ ≤ (momentTightG P g p L (x:ℂ)).re :=
  positive_series_circle_norm_le _ x hx.1 (momentTightG_real_nonnegative_coefficients P g p hp hs L)
    (fun z hz => momentTightG_taylor P g p L z (hz.trans_lt hx.2)) z hz

lemma centeredTightGenerating_analytic_disk (P : PsiTheory) (g p : ℕ) (hp : 1≤p) (hs : Stable g p) (L : Fin p → ℝ)
    (x μ σ R : ℝ) (hx : 0 ≤ x)
    (htilt : ∀ w : ℂ, ‖w‖ < R → x*Real.exp (w.re/σ) < xCritical) :
    AnalyticOnNhd ℂ (centeredTightGenerating P g p L x μ σ) (Metric.ball 0 R) := by
  intro w hw
  have hn : ‖w‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hw
  have harg : ‖(x:ℂ)*Complex.exp (w/(σ:ℂ))‖ < xCritical := by
    rw [norm_mul,Complex.norm_of_nonneg hx,Complex.norm_exp,Complex.div_ofReal_re]
    exact htilt w hn
  apply AnalyticAt.mul (by fun_prop)
  have hinner : AnalyticAt ℂ (fun v : ℂ => (x:ℂ)*Complex.exp (v/(σ:ℂ))) w := by fun_prop
  have hcomp := AnalyticAt.comp (g := momentTightG P g p L)
    (f := fun v : ℂ => (x:ℂ)*Complex.exp (v/(σ:ℂ)))
    (momentTightG_analyticAt P g p L _ harg) hinner
  exact hcomp.div_const

lemma centeredTightGenerating_norm_domination (P : PsiTheory) (g p : ℕ) (hp : 1≤p) (hs : Stable g p) (L : Fin p → ℝ)
    (x μ σ : ℝ) (hx : x ∈ Ico 0 xCritical) (hGx : 0 < (momentTightG P g p L (x:ℂ)).re)
    (w : ℂ) (hwt : x*Real.exp (w.re/σ) ∈ Ico 0 xCritical) :
    ‖centeredTightGenerating P g p L x μ σ w‖ ≤
      ‖centeredTightGenerating P g p L x μ σ (w.re:ℂ)‖ := by
  have hnorm (y : ℝ) (hy : y ∈ Ico 0 xCritical) :
      ‖momentTightG P g p L (y:ℂ)‖ = (momentTightG P g p L (y:ℂ)).re := by
    have him := momentTightG_ofReal_im_zero P g p L y hy
    have hnon : 0 ≤ (momentTightG P g p L (y:ℂ)).re := by
      exact le_trans (norm_nonneg _) (momentTightG_disk_domination P g p hp hs L y hy (y:ℂ)
        (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hy.1] using (le_rfl : y ≤ y)))
    have he : momentTightG P g p L (y:ℂ) = Complex.ofReal (momentTightG P g p L (y:ℂ)).re := by
      apply Complex.ext
      · rfl
      · simpa using him
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnon]
    simp only [Complex.ofReal_re]
  have hz : ‖(x:ℂ)*Complex.exp (w/(σ:ℂ))‖ = x*Real.exp (w.re/σ) := by
    rw [norm_mul,Complex.norm_of_nonneg hx.1,Complex.norm_exp,Complex.div_ofReal_re]
  have htilt : (x:ℂ)*Complex.exp ((w.re:ℂ)/(σ:ℂ)) =
      ((x*Real.exp (w.re/σ):ℝ):ℂ) := by
    rw [←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
  have hexp : ‖Complex.exp (-(μ:ℂ)*w/(σ:ℂ))‖ =
      ‖Complex.exp (-(μ:ℂ)*(w.re:ℂ)/(σ:ℂ))‖ := by
    simp only [Complex.norm_exp,Complex.div_ofReal_re,Complex.mul_re,Complex.neg_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.neg_im,neg_zero,zero_mul,sub_zero]
  unfold centeredTightGenerating
  rw [norm_mul,norm_mul,hexp,norm_div,norm_div,htilt,hnorm _ hwt]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact momentTightG_disk_domination P g p hp hs L _ hwt _ hz.le


end WP.TightConnected
