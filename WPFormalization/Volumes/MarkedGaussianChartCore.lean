import WPFormalization.Volumes.LeadingMarkedComparison
import WPFormalization.Analysis.ScaledGaussianModelError
/-! Actual marked central error on a supplied genuine leading Gaussian
chart. The previously proved K=0 marked error, positive-series domination
and analytic chart jets control the true characteristic function. Global
chart existence is a separate local-data theorem, not an extra assumption
of the final paper proposition. -/
noncomputable section
namespace WP
open Set Complex
set_option autoImplicit false

lemma marked_gaussian_chart_core_error (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (C₀:ℝ)(hC₀:0<C₀)(hh:0<(complexity g p:ℝ))(hε:2*C₀≤(complexity g p:ℝ))
    (hrel:∀x∈Ico (0:ℝ) xCritical,|markedLeadingError P g p x|≤C₀/(complexity g p:ℝ))
    (x μ σ ρ C D m T:ℝ)(hx:x∈Ico (0:ℝ) xCritical)
    (hρ:0<ρ)(hC:0<C)(hD:0<D)(hm:0 < m)(hT:1≤T)
    (hwindow:32*T≤ρ*Real.sqrt m)(hsmall:4*C*T^3/(ρ*Real.sqrt m)≤1)
    (L A:ℂ→ℂ)
    (hLa:AnalyticOnNhd ℂ L (Metric.ball 0 (ρ*Real.sqrt m)))
    (hAa:AnalyticOnNhd ℂ A (Metric.ball 0 (ρ*Real.sqrt m)))
    (hL0:L 0=0)(hL1:WP.coeff L 1=0)(hL2:WP.coeff L 2=(1/2:ℂ))(hA0:A 0=1)
    (hbL:∀w:ℂ,‖w‖<ρ*Real.sqrt m→‖L w‖≤C*‖w‖^2)
    (hbA:∀w:ℂ,‖w‖<ρ*Real.sqrt m→‖A w‖≤D)
    (htrace:∀u:ℝ,|u|<ρ*Real.sqrt m→
      x*Real.exp (u/σ)∈Ioo (0:ℝ) xCritical ∧
      Complex.exp (L (u:ℂ))*A (u:ℂ)=
        ((Real.exp (-μ*u/σ)*markedModel g p (inverseY (x*Real.exp (u/σ)))/
          markedModel g p (inverseY x):ℝ):ℂ))
    (t:ℝ)(ht:|t|≤T):
    ‖realCenteredMarkedGenerating P g p x μ σ ((t:ℂ)*Complex.I)-Complex.exp (-(t:ℂ)^2/2)‖≤
      4*D*Real.sqrt (C₀/(complexity g p:ℝ))*Real.exp (256*C*T^2)+
        (8*C*D*T^3+4*D*T)/(ρ*Real.sqrt m):=by
  let M:ℂ→ℂ:=fun z=>Complex.exp (L z)*A z
  let G:ℝ:=D*Real.exp (256*C*T^2)
  have hTp:0<T:=zero_lt_one.trans_le hT
  have hRadius:16*T<ρ*Real.sqrt m:=by linarith
  have hMs:AnalyticOnNhd ℂ M (Metric.ball 0 (16*T)):=by
    intro z hz
    have hn:‖z‖<16*T:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    have hzr:z∈Metric.ball (0:ℂ) (ρ*Real.sqrt m):=by
      simpa only[Metric.mem_ball,dist_zero_right] using hn.trans hRadius
    exact (hLa z hzr).cexp.mul (hAa z hzr)
  have hMb:∀z:ℂ,‖z‖<16*T→‖M z‖≤G:=by
    intro z hz
    have hzR:‖z‖<ρ*Real.sqrt m:=hz.trans hRadius
    have hnorm:‖Complex.exp (L z)‖≤Real.exp (256*C*T^2):=by
      rw[Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hl: (L z).re≤C*‖z‖^2:=(Complex.re_le_norm _).trans (hbL z hzR)
      have hsq:‖z‖^2≤(16*T)^2:=by nlinarith[norm_nonneg z]
      nlinarith[mul_le_mul_of_nonneg_left hsq hC.le]
    dsimp only[M,G]
    rw[norm_mul]
    exact (mul_le_mul hnorm (hbA z hzR) (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)
  have htilt:∀z:ℂ,‖z‖<16*T→x*Real.exp (z.re/σ)∈Ico (0:ℝ) xCritical:=by
    intro z hz
    have hr:|z.re|<ρ*Real.sqrt m:=(Complex.abs_re_le_norm z).trans_lt (hz.trans hRadius)
    exact ⟨(htrace z.re hr).1.1.le,(htrace z.re hr).1.2⟩
  have hMtrace:∀u:ℝ,|u|<16*T→M (u:ℂ)=
      ((Real.exp (-μ*u/σ)*markedModel g p (inverseY (x*Real.exp (u/σ)))/
        markedModel g p (inverseY x):ℝ):ℂ):=by
    intro u hu
    exact (htrace u (hu.trans hRadius)).2
  have hw:‖(t:ℂ)*Complex.I‖≤3*T/2:=by
    rw[norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    linarith
  have hcomp:=marked_leading_slit_comparison P g p hp hs C₀ hC₀ hh hε hrel x μ σ T G hx hTp
    (by dsimp[G];positivity) M hMs hMb htilt hMtrace _ hw
  have hmodel:=Analysis.scaled_gaussian_model_core_error L A ρ C D m T hρ hC hD hm hT hwindow hsmall
    hLa hAa hL0 hL1 hL2 hA0 hbL hbA t ht
  have hsum:=norm_sub_le_norm_sub_add_norm_sub
    (realCenteredMarkedGenerating P g p x μ σ ((t:ℂ)*Complex.I)) (M ((t:ℂ)*Complex.I))
    (Complex.exp (-(t:ℂ)^2/2))
  apply (hsum.trans (add_le_add hcomp hmodel)).trans_eq
  dsimp[G]
  ring


lemma scaledMarkedFourier_eq_real_centered (P:PsiTheory)(g p:ℕ)(x t:ℝ)
    (ht:|t|≤Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)):
    scaledMarkedFourier P g p x t=
      realCenteredMarkedGenerating P g p x ((complexity g p:ℝ)*Psi x)
        (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) ((t:ℂ)*Complex.I):=by
  have hmem:t∈Icc (-(Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)))
      (Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)):=abs_le.mp ht
  unfold scaledMarkedFourier Analysis.scaledCenteredFourier realCenteredMarkedGenerating markedPGF
  rw[Set.indicator_of_mem hmem,Complex.ofReal_div]
  congr 2 <;>ring
end WP
