import WPFormalization.Volumes.PositiveConvolutionProof
import WPFormalization.Volumes.PointMassFourier
/-! Actual marked generating functions: nonnegative real Taylor coefficients,
convergence throughout the genuine cusp disk, and positive-series domination
of centered complex tilts by their real tilts. Stable genus-zero marking counts
are retained; the complex tilt must stay within the actual convergence disk. -/

noncomputable section
namespace WP
open Set
lemma marked_generating_analytic_disk (P:PsiTheory) (g p:ℕ):
    AnalyticOnNhd ℂ (iteratedDeriv p (Phi P g)) (Metric.ball 0 xCritical):=by
  intro z hz
  have hn:‖z‖<xCritical:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
  simpa only[iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P g z hn).iterated_deriv p

lemma marked_generating_nonnegative_coefficients (P:PsiTheory) (g p:ℕ)
    (hp:1≤p) (hs:Stable g p):
    ∀j:ℕ,0≤realCoeff (iteratedDeriv p (Phi P g)) j ∧
      (WP.coeff (iteratedDeriv p (Phi P g)) j).im=0:=by
  intro j
  have hsj:Stable g (j+p):=by unfold Stable at *;omega
  have h0:(0:ℝ)∈Ico (0:ℝ) xCritical:=⟨le_rfl,Analysis.xCritical_pos_parameter⟩
  have he:WP.coeff (iteratedDeriv p (Phi P g)) j=
      ((shifted P g (List.replicate (j+p) 0) 0/(j.factorial:ℝ):ℝ):ℂ):=by
    rw[WP.coeff,Analysis.iteratedDeriv_iteratedDeriv_eq]
    rw[show (0:ℂ)=((0:ℝ):ℂ) from rfl,
      PositiveConvolution.Phi_iteratedDeriv_ofReal P g (j+p) hsj 0 h0,
      Analysis.inverseY_zero_value]
    norm_cast
  have hnon:0≤ shifted P g (List.replicate (j+p) 0) 0:=
    shifted_zero_nonneg_nonempty P g (j+p) (by omega) 0 ⟨le_rfl,y₀_pos⟩
  change 0≤(WP.coeff (iteratedDeriv p (Phi P g)) j).re ∧ _
  rw[he,Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨div_nonneg hnon (Nat.cast_nonneg _),rfl⟩

lemma marked_generating_hasSum (P:PsiTheory) (g p:ℕ) (z:ℂ) (hz:‖z‖<xCritical):
    HasSum (fun j=>WP.coeff (iteratedDeriv p (Phi P g)) j*z^j)
      (iteratedDeriv p (Phi P g) z):=by
  exact PositiveConvolution.analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (fun w hw=>marked_generating_analytic_disk P g p w (by simpa only[Metric.mem_ball,dist_zero_right] using hw)) z hz

lemma marked_generating_disk_domination (P:PsiTheory) (g p:ℕ)
    (hp:1≤p) (hs:Stable g p) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (z:ℂ) (hz:‖z‖≤x):
    ‖iteratedDeriv p (Phi P g) z‖≤ markedF P g p x:=by
  exact PositiveConvolution.positive_series_circle_norm_le _ x hx.1
    (marked_generating_nonnegative_coefficients P g p hp hs)
    (fun w hw=>marked_generating_hasSum P g p w (hw.trans_lt hx.2)) z hz
end WP

namespace WP
open Set
lemma markedF_positive_cusp_weight (P:PsiTheory) (g p:ℕ) (hp:1≤p)
    (hs:Stable g p) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    0< markedF P g p x:=by
  have hb:=inverseY_branch x hx
  have ht:=markedF_pos_parameter P g p hp hs (inverseY x) hb.1
  simpa only[hb.2] using ht

lemma marked_generating_norm_real (P:PsiTheory) (g p:ℕ) (hp:1≤p)
    (hs:Stable g p) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    ‖iteratedDeriv p (Phi P g) (x:ℂ)‖=markedF P g p x:=by
  have he:=PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs x hx
  rw[he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (shifted_zero_pos_nonempty P g p hp hs (inverseY x) (inverseY_branch x hx).1)]
  have hreal:=congrArg Complex.re he
  simpa only[markedF,Complex.ofReal_re] using hreal.symm

def centeredMarkedGenerating (P:PsiTheory) (g p k:ℕ) (x σ:ℝ) (w:ℂ):ℂ:=
  Complex.exp (-(k:ℂ)*w/(σ:ℂ))*
    (iteratedDeriv p (Phi P g) ((x:ℂ)*Complex.exp (w/(σ:ℂ)))/
      iteratedDeriv p (Phi P g) (x:ℂ))

lemma marked_tilted_disk_domination (P:PsiTheory) (g p k:ℕ) (hp:1≤p)
    (hs:Stable g p) (x σ:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (w:ℂ) (hwt:x*Real.exp (w.re/σ)∈Ico (0:ℝ) xCritical):
    ‖centeredMarkedGenerating P g p k x σ w‖≤
      Real.exp (-(k:ℝ)*w.re/σ)*markedF P g p (x*Real.exp (w.re/σ))/markedF P g p x:=by
  have hz:‖(x:ℂ)*Complex.exp (w/(σ:ℂ))‖=x*Real.exp (w.re/σ):=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1,Complex.norm_exp,Complex.div_ofReal_re]
  have hpfx:‖Complex.exp (-(k:ℂ)*w/(σ:ℂ))‖=Real.exp (-(k:ℝ)*w.re/σ):=by
    rw[Complex.norm_exp,Complex.div_ofReal_re]
    congr 1
    simp only[Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.natCast_re,Complex.natCast_im,neg_zero,zero_mul,sub_zero]
  have hfd:=marked_generating_disk_domination P g p hp hs _ hwt _ hz.le
  unfold centeredMarkedGenerating
  rw[norm_mul,norm_div,hpfx,marked_generating_norm_real P g p hp hs x hx]
  have ht:=mul_le_mul_of_nonneg_left hfd (Real.exp_pos (-(k:ℝ)*w.re/σ)).le
  have hfp:=markedF_positive_cusp_weight P g p hp hs x hx
  convert div_le_div_of_nonneg_right ht hfp.le using 1 <;>ring
end WP

namespace WP
open Set
lemma centeredMarkedGenerating_norm_real (P:PsiTheory) (g p k:ℕ)
    (hp:1≤p) (hs:Stable g p) (x σ u:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (hxu:x*Real.exp (u/σ)∈Ico (0:ℝ) xCritical):
    ‖centeredMarkedGenerating P g p k x σ (u:ℂ)‖=
      Real.exp (-(k:ℝ)*u/σ)*markedF P g p (x*Real.exp (u/σ))/markedF P g p x:=by
  unfold centeredMarkedGenerating
  rw[norm_mul,norm_div,marked_generating_norm_real P g p hp hs x hx]
  have he:‖Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ))‖=Real.exp (-(k:ℝ)*u/σ):=by
    rw[Complex.norm_exp]
    congr 1
    simp only[Complex.div_ofReal_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
      Complex.natCast_re,Complex.natCast_im,Complex.ofReal_re,Complex.ofReal_im,
      neg_zero,zero_mul,sub_zero]
  have hz:(x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ))=((x*Real.exp (u/σ):ℝ):ℂ):=by
    rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
  rw[he,hz,marked_generating_norm_real P g p hp hs _ hxu]
  ring

lemma centeredMarkedGenerating_norm_domination (P:PsiTheory) (g p k:ℕ)
    (hp:1≤p) (hs:Stable g p) (x σ:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (w:ℂ) (hwt:x*Real.exp (w.re/σ)∈Ico (0:ℝ) xCritical):
    ‖centeredMarkedGenerating P g p k x σ w‖≤
      ‖centeredMarkedGenerating P g p k x σ (w.re:ℂ)‖:=by
  rw[centeredMarkedGenerating_norm_real P g p k hp hs x σ w.re hx hwt]
  exact marked_tilted_disk_domination P g p k hp hs x σ hx w hwt

lemma centeredMarkedGenerating_analytic_disk (P:PsiTheory) (g p k:ℕ)
    (x σ R:ℝ) (hx:0≤x)
    (htilt:∀w:ℂ,‖w‖<R→x*Real.exp (w.re/σ)<xCritical):
    AnalyticOnNhd ℂ (centeredMarkedGenerating P g p k x σ) (Metric.ball 0 R):=by
  intro w hw
  have hw':‖w‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
  have hz:‖(x:ℂ)*Complex.exp (w/(σ:ℂ))‖<xCritical:=by
    rw[norm_mul,Complex.norm_of_nonneg hx,Complex.norm_exp,Complex.div_ofReal_re]
    exact htilt w hw'
  have hcomp:AnalyticAt ℂ (fun w:ℂ=>iteratedDeriv p (Phi P g) ((x:ℂ)*Complex.exp (w/(σ:ℂ)))) w:=
    ((marked_generating_analytic_disk P g p) _ (by simpa only[Metric.mem_ball,dist_zero_right] using hz)).comp (by fun_prop)
  unfold centeredMarkedGenerating
  exact (by fun_prop:AnalyticAt ℂ (fun w:ℂ=>Complex.exp (-(k:ℂ)*w/(σ:ℂ))) w).mul
    (hcomp.div_const)
end WP
