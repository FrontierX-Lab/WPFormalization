import WPFormalization.Volumes.MarkedFourierInversion
/-! Actual complex tilts centered at any real value, with analytic-domain
and positive-series domination proofs. In particular the true mean need
not be representable by an integer coefficient index. -/
noncomputable section
namespace WP
open Set

def realCenteredMarkedGenerating (P:PsiTheory)(g p:ℕ)(x μ σ:ℝ)(w:ℂ):ℂ:=
  Complex.exp (-(μ:ℂ)*w/(σ:ℂ))*markedPGF P g p x (Complex.exp (w/(σ:ℂ)))

lemma realCenteredMarkedGenerating_norm_real (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (x μ σ u:ℝ)(hx:x∈Ico (0:ℝ) xCritical)
    (hxu:x*Real.exp (u/σ)∈Ico (0:ℝ) xCritical):
    ‖realCenteredMarkedGenerating P g p x μ σ (u:ℂ)‖=
      Real.exp (-μ*u/σ)*markedF P g p (x*Real.exp (u/σ))/markedF P g p x:=by
  unfold realCenteredMarkedGenerating markedPGF
  rw[norm_mul,norm_div,marked_generating_norm_real P g p hp hs x hx]
  have he:‖Complex.exp (-(μ:ℂ)*(u:ℂ)/(σ:ℂ))‖=Real.exp (-μ*u/σ):=by
    rw[Complex.norm_exp]
    congr 1
    simp
  have hz:(x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ))=((x*Real.exp (u/σ):ℝ):ℂ):=by
    rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
  rw[he,hz,marked_generating_norm_real P g p hp hs _ hxu]
  ring

lemma realCenteredMarkedGenerating_norm_domination (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (x μ σ:ℝ)(hx:x∈Ico (0:ℝ) xCritical)(w:ℂ)
    (hwt:x*Real.exp (w.re/σ)∈Ico (0:ℝ) xCritical):
    ‖realCenteredMarkedGenerating P g p x μ σ w‖≤
      ‖realCenteredMarkedGenerating P g p x μ σ (w.re:ℂ)‖:=by
  rw[realCenteredMarkedGenerating_norm_real P g p hp hs x μ σ w.re hx hwt]
  unfold realCenteredMarkedGenerating markedPGF
  rw[norm_mul,norm_div,marked_generating_norm_real P g p hp hs x hx]
  have hz:‖(x:ℂ)*Complex.exp (w/(σ:ℂ))‖=x*Real.exp (w.re/σ):=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1,Complex.norm_exp,Complex.div_ofReal_re]
  have he:‖Complex.exp (-(μ:ℂ)*w/(σ:ℂ))‖=Real.exp (-μ*w.re/σ):=by
    rw[Complex.norm_exp]
    congr 1
    simp [Complex.div_ofReal_re,mul_comm,mul_left_comm,mul_assoc]
  rw[he]
  convert mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (marked_generating_disk_domination P g p hp hs _ hwt _ hz.le)
      (markedF_positive_cusp_weight P g p hp hs x hx).le) (Real.exp_pos (-μ*w.re/σ)).le using 1 <;>ring

lemma realCenteredMarkedGenerating_analytic_disk (P:PsiTheory)(g p:ℕ)(x μ σ R:ℝ)(hx:0≤x)
    (htilt:∀w:ℂ,‖w‖<R→x*Real.exp (w.re/σ)<xCritical):
    AnalyticOnNhd ℂ (realCenteredMarkedGenerating P g p x μ σ) (Metric.ball 0 R):=by
  have ha:=centeredMarkedGenerating_analytic_disk P g p 0 x σ R hx htilt
  intro w hw
  have hf:AnalyticAt ℂ (fun z:ℂ=>markedPGF P g p x (Complex.exp (z/(σ:ℂ)))) w:=by
    have he:(fun z:ℂ=>markedPGF P g p x (Complex.exp (z/(σ:ℂ))))=centeredMarkedGenerating P g p 0 x σ:=by
      funext z
      simp [centeredMarkedGenerating,markedPGF]
    rw[he]
    exact ha w hw
  exact (by fun_prop:AnalyticAt ℂ (fun z:ℂ=>Complex.exp (-(μ:ℂ)*z/(σ:ℂ))) w).mul hf

lemma realCenteredMarkedGenerating_real (P:PsiTheory)(g p:ℕ)(hs:Stable g p)
    (x μ σ u:ℝ)(hx:x∈Ico (0:ℝ) xCritical)
    (hxu:x*Real.exp (u/σ)∈Ico (0:ℝ) xCritical):
    realCenteredMarkedGenerating P g p x μ σ (u:ℂ)=
      ((Real.exp (-μ*u/σ)*markedF P g p (x*Real.exp (u/σ))/markedF P g p x:ℝ):ℂ):=by
  have hre (v:ℝ)(hv:v∈Ico (0:ℝ) xCritical):
      iteratedDeriv p (Phi P g) (v:ℂ)=(markedF P g p v:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using congrArg Complex.im
        (PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs v hv)
  unfold realCenteredMarkedGenerating markedPGF
  rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul,hre _ hxu,hre _ hx]
  have he:-(μ:ℂ)*(u:ℂ)/(σ:ℂ)=((-μ*u/σ:ℝ):ℂ):=by push_cast;ring
  rw[he,←Complex.ofReal_exp]
  push_cast
  ring
end WP
