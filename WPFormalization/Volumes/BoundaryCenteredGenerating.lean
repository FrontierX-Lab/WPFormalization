import WPFormalization.Volumes.BoundaryPositiveConvolution
import WPFormalization.Volumes.PointMassFourier
import WPFormalization.Analysis.SlitDiskComparison

/-! The actual boundary insertion inherits positive-series control of complex
tilts. Real-axis comparison can therefore be transferred by the already
proved slit-disk estimate, without an extra probability limit theorem. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

def centeredBoundaryGenerating (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (x μ σ : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(μ:ℂ)*w/(σ:ℂ)) *
    (boundaryG P g p L ((x:ℂ)*Complex.exp (w/(σ:ℂ)))/boundaryG P g p L (x:ℂ))

lemma boundaryG_taylor (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (z : ℂ) (hz : ‖z‖ < xCritical) :
    HasSum (fun j => WP.coeff (boundaryG P g p L) j*z^j) (boundaryG P g p L z) :=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (boundaryG_analyticAt P g p L) z hz

lemma boundaryG_real_nonnegative_coefficients (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ) :
    ∀ j, 0 ≤ realCoeff (boundaryG P g p L) j ∧ (WP.coeff (boundaryG P g p L) j).im=0 :=
  (boundaryG_positiveJets P g p L).coefficient_nonneg

lemma boundaryG_ofReal_im_zero (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (x : ℝ) (hx : x ∈ Ico 0 xCritical) : (boundaryG P g p L (x:ℂ)).im=0 := by
  have hz : ‖(x:ℂ)‖ < xCritical := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hs := Complex.imCLM.hasSum (boundaryG_taylor P g p L (x:ℂ) hz)
  have he (j : ℕ) : (WP.coeff (boundaryG P g p L) j*(x:ℂ)^j).im=0 := by
    simp only [Complex.mul_im,←Complex.ofReal_pow,Complex.ofReal_im,
      (boundaryG_real_nonnegative_coefficients P g p L j).2,zero_mul,mul_zero,add_zero]
  change HasSum (fun j => (WP.coeff (boundaryG P g p L) j*(x:ℂ)^j).im)
    (boundaryG P g p L (x:ℂ)).im at hs
  have hs0 : HasSum (fun _ : ℕ => (0:ℝ)) (boundaryG P g p L (x:ℂ)).im := by
    convert hs using 1
    ext j
    exact (he j).symm
  exact (hasSum_zero.unique hs0).symm

lemma boundaryG_disk_domination (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (x : ℝ) (hx : x ∈ Ico 0 xCritical) (z : ℂ) (hz : ‖z‖ ≤ x) :
    ‖boundaryG P g p L z‖ ≤ (boundaryG P g p L (x:ℂ)).re :=
  positive_series_circle_norm_le _ x hx.1 (boundaryG_real_nonnegative_coefficients P g p L)
    (fun z hz => boundaryG_taylor P g p L z (hz.trans_lt hx.2)) z hz

lemma centeredBoundaryGenerating_analytic_disk (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (x μ σ R : ℝ) (hx : 0 ≤ x)
    (htilt : ∀ w : ℂ, ‖w‖ < R → x*Real.exp (w.re/σ) < xCritical) :
    AnalyticOnNhd ℂ (centeredBoundaryGenerating P g p L x μ σ) (Metric.ball 0 R) := by
  intro w hw
  have hn : ‖w‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hw
  have harg : ‖(x:ℂ)*Complex.exp (w/(σ:ℂ))‖ < xCritical := by
    rw [norm_mul,Complex.norm_of_nonneg hx,Complex.norm_exp,Complex.div_ofReal_re]
    exact htilt w hn
  apply AnalyticAt.mul (by fun_prop)
  have hinner : AnalyticAt ℂ (fun v : ℂ => (x:ℂ)*Complex.exp (v/(σ:ℂ))) w := by fun_prop
  have hcomp := AnalyticAt.comp (g := boundaryG P g p L)
    (f := fun v : ℂ => (x:ℂ)*Complex.exp (v/(σ:ℂ)))
    (boundaryG_analyticAt P g p L _ harg) hinner
  exact hcomp.div_const

lemma centeredBoundaryGenerating_norm_domination (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (x μ σ : ℝ) (hx : x ∈ Ico 0 xCritical) (hGx : 0 < (boundaryG P g p L (x:ℂ)).re)
    (w : ℂ) (hwt : x*Real.exp (w.re/σ) ∈ Ico 0 xCritical) :
    ‖centeredBoundaryGenerating P g p L x μ σ w‖ ≤
      ‖centeredBoundaryGenerating P g p L x μ σ (w.re:ℂ)‖ := by
  have hnorm (y : ℝ) (hy : y ∈ Ico 0 xCritical) :
      ‖boundaryG P g p L (y:ℂ)‖ = (boundaryG P g p L (y:ℂ)).re := by
    have him := boundaryG_ofReal_im_zero P g p L y hy
    have hnon : 0 ≤ (boundaryG P g p L (y:ℂ)).re := by
      exact le_trans (norm_nonneg _) (boundaryG_disk_domination P g p L y hy (y:ℂ)
        (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hy.1] using (le_rfl : y ≤ y)))
    have he : boundaryG P g p L (y:ℂ) = Complex.ofReal (boundaryG P g p L (y:ℂ)).re := by
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
  unfold centeredBoundaryGenerating
  rw [norm_mul,norm_mul,hexp,norm_div,norm_div,htilt,hnorm _ hwt]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact boundaryG_disk_domination P g p L _ hwt _ hz.le

end WP.BoundaryConvolution
