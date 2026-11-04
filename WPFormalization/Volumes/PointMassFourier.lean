import WPFormalization.Analysis.HarmonicFourierScaling
import WPFormalization.Volumes.PositiveConvolutionAnalytic
noncomputable section
namespace WP.PositiveConvolution
open Set MeasureTheory
lemma positive_series_circle_norm_le (R:ℂ→ℂ) (x:ℝ)
    (hx:0≤x) (ha:∀n,0≤realCoeff R n ∧ (WP.coeff R n).im=0)
    (hseries:∀z:ℂ,‖z‖≤x→HasSum (fun n=>WP.coeff R n*z^n) (R z))
    (z:ℂ) (hz:‖z‖≤x):‖R z‖≤(R x).re:=by
  have hr:=Complex.reCLM.hasSum (hseries (x:ℂ) (by simp only[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx]; exact le_rfl))
  change HasSum (fun n=>(WP.coeff R n*(x:ℂ)^n).re) (R x).re at hr
  apply (hseries z hz).norm_le_of_bounded hr
  intro n
  have he:WP.coeff R n=Complex.ofReal (realCoeff R n):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using (ha n).2
  rw[he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha n).1,norm_pow,
    ←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (ha n).1
lemma positive_series_circle_domination (V R:ℂ→ℂ) (x:ℝ) (H:ℕ)
    (hx:0≤x) (hV:0<(V x).re) (hVi:(V x).im=0)
    (hR:0<(R x).re) (hRi:(R x).im=0)
    (ha:∀n,0≤realCoeff R n ∧ (WP.coeff R n).im=0)
    (hseries:∀z:ℂ,‖z‖≤x→HasSum (fun n=>WP.coeff R n*z^n) (R z))
    (z:ℂ) (hz:‖z‖≤x):
    ‖V z^H*R z‖ / (V x^H*R x).re ≤ ‖V z / V x‖^H:=by
  have hVe:V x=Complex.ofReal ((V x).re):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using hVi
  have hRe:R x=Complex.ofReal ((R x).re):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using hRi
  have hd:(V x^H*R x).re=(V x).re^H*(R x).re:=by
    conv_lhs=>rw[hVe,hRe,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
  have hnorm:‖V x‖=(V x).re:=by
    conv_lhs=>rw[hVe,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV]
  rw[hd,norm_mul,norm_pow,norm_div,div_pow,hnorm]
  apply (div_le_iff₀ (mul_pos (pow_pos hV H) hR)).2
  calc
    ‖V z‖^H*‖R z‖ ≤ ‖V z‖^H*(R x).re :=
      mul_le_mul_of_nonneg_left (positive_series_circle_norm_le R x hx ha hseries z hz) (pow_nonneg (norm_nonneg _) _)
    _ = ‖V z‖^H/(V x).re^H*((V x).re^H*(R x).re):=by
      field_simp
lemma realCoeff_circle_integral_bound (f:ℂ→ℂ) (ρ x:ℝ)
    (hx:0<x) (hxr:x<ρ) (hf:AnalyticOnNhd ℂ f (Metric.ball 0 ρ)) (n:ℕ):
    realCoeff f n*x^n ≤ (2*Real.pi)⁻¹ *
      ∫θ:ℝ in (-Real.pi)..Real.pi,‖f ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖:=by
  let g:ℂ→ℂ:=fun w=>f ((x:ℂ)*w)
  have hg:DifferentiableOn ℂ g (Metric.closedBall 0 1):=by
    intro w hw
    have hn:‖(x:ℂ)*w‖<ρ:=by
      have hw':‖w‖≤1:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hw
      rw[norm_mul,Complex.norm_of_nonneg hx.le]
      exact (mul_le_of_le_one_right hx.le hw').trans_lt hxr
    exact ((hf _ (by simpa only[Metric.mem_ball,dist_zero_right] using hn)).differentiableAt.comp w
      (by fun_prop : DifferentiableAt ℂ (fun w:ℂ=>(x:ℂ)*w) w)).differentiableWithinAt
  have he:=Analysis.coeff_eq_symmetric_fourier_integral g hg n
  have hn:realCoeff g n≤‖WP.coeff g n‖:=Complex.re_le_norm _
  rw[he,norm_mul,norm_inv,Complex.norm_of_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)] at hn
  have hnorm: (fun θ:ℝ=>‖Complex.exp (-(n:ℂ)*(θ:ℂ)*Complex.I)*g (Complex.exp ((θ:ℂ)*Complex.I))‖)=
      fun θ:ℝ=>‖g (Complex.exp ((θ:ℂ)*Complex.I))‖:=by
    funext θ
    rw[norm_mul]
    have hex:‖Complex.exp (-(n:ℂ)*(θ:ℂ)*Complex.I)‖=1:=by
      convert Complex.norm_exp_ofReal_mul_I (-(n:ℝ)*θ) using 1 <;>push_cast <;>ring
    rw[hex,one_mul]
  have hi:=intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (by linarith[Real.pi_pos]:-Real.pi≤Real.pi)
    (f:=fun θ:ℝ=>Complex.exp (-(n:ℂ)*(θ:ℂ)*Complex.I)*g (Complex.exp ((θ:ℂ)*Complex.I)))
  rw[hnorm] at hi
  have hcoef:realCoeff g n=x^n*realCoeff f n:=Analysis.realCoeff_comp_mul_left f x n
  rw[hcoef] at hn
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (mul_nonneg (by norm_num : (0:ℝ)≤2) Real.pi_pos.le))
  have hfinal := hn.trans hh
  simpa only[g,mul_comm (x^n)] using hfinal
lemma realCoeff_normalized_circle_bound (f:ℂ→ℂ) (ρ x:ℝ)
    (hx:0<x) (hxr:x<ρ) (hf:AnalyticOnNhd ℂ f (Metric.ball 0 ρ))
    (hd:0<(f x).re) (n:ℕ):
    realCoeff f n*x^n/(f x).re ≤ (2*Real.pi)⁻¹ *
      ∫θ:ℝ in (-Real.pi)..Real.pi,
        ‖f ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖/(f x).re:=by
  have he:=div_le_div_of_nonneg_right (realCoeff_circle_integral_bound f ρ x hx hxr hf n) hd.le
  rw[intervalIntegral.integral_div]
  simpa only[mul_div_assoc] using he
end WP.PositiveConvolution
namespace WP.PositiveConvolution
open Set MeasureTheory
lemma point_mass_fourier_reduction (P:PsiTheory) (H:ℕ) (x:ℝ)
    (hx:x∈Ioo 0 xCritical) (R:ℂ→ℂ)
    (hR:AnalyticOnNhd ℂ R (Metric.ball 0 xCritical))
    (ha:∀n,0≤realCoeff R n∧(WP.coeff R n).im=0)
    (hRp:0<(R x).re) (hRi:(R x).im=0)
    (hseries:∀z:ℂ,‖z‖<xCritical→HasSum (fun n=>WP.coeff R n*z^n) (R z)) (n:ℕ):
    realCoeff (fun z=>universalV P z^H*R z) n*x^n/
      (universalV P x^H*R x).re ≤ (2*Real.pi)⁻¹ *
      ∫θ:ℝ in (-Real.pi)..Real.pi,
        ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H:=by
  have hV:AnalyticOnNhd ℂ (universalV P) (Metric.ball 0 xCritical):=by
    intro z hz
    have hn:‖z‖<xCritical:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z
    simpa only[iteratedDeriv_eq_iterate] using
      (Phi_analyticAt_open_disk P 0 z hn).iterated_deriv 3
  have hf:AnalyticOnNhd ℂ (fun z=>universalV P z^H*R z) (Metric.ball 0 xCritical):=
    hV.pow H |>.mul hR
  have hVr:universalV P x=Complex.ofReal ((a (inverseY x))⁻¹):=
    planarThird_ofReal P x ⟨hx.1.le,hx.2⟩
  have hVp:0<(universalV P x).re:=by
    rw[hVr,Complex.ofReal_re]
    exact inv_pos.mpr (a_pos _ (inverseY_branch x ⟨hx.1.le,hx.2⟩).1)
  have hVi:(universalV P x).im=0:=by rw[hVr,Complex.ofReal_im]
  have hRe:R x=Complex.ofReal ((R x).re):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using hRi
  have hd:0<(universalV P x^H*R x).re:=by
    rw[hVr,hRe,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
    exact mul_pos (pow_pos (by simpa only[hVr,Complex.ofReal_re] using hVp) _) hRp
  have hnorm(θ:ℝ):‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖=x:=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
  have hc:Continuous (fun θ:ℝ=>universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))):=by
    rw[continuous_iff_continuousAt]
    intro θ
    exact (hV _ (by simpa only[Metric.mem_ball,dist_zero_right,hnorm] using hx.2)).continuousAt.comp
      (by fun_prop)
  have hfc:Continuous (fun θ:ℝ=>universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))^H*
      R ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))):=by
    apply (hc.pow H).mul
    rw[continuous_iff_continuousAt]
    intro θ
    exact (hR _ (by simpa only[Metric.mem_ball,dist_zero_right,hnorm] using hx.2)).continuousAt.comp
      (by fun_prop)
  have hi:=intervalIntegral.integral_mono_on (μ:=volume) (by linarith[Real.pi_pos]:-Real.pi≤Real.pi)
    ((hfc.norm.div_const _).intervalIntegrable _ _)
    (((hc.div_const _).norm.pow H).intervalIntegrable _ _)
    (fun θ hθ=>positive_series_circle_domination (universalV P) R x H hx.1.le hVp hVi hRp hRi ha
      (fun z hz=>hseries z (hz.trans_lt hx.2)) _ (hnorm θ).le)
  exact (realCoeff_normalized_circle_bound _ xCritical x hx.1 hx.2 hf hd n).trans
    (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)))
end WP.PositiveConvolution
