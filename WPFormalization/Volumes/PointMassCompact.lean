import WPFormalization.Volumes.PlanarInverseBoundary
import WPFormalization.Analysis.PositiveSeriesCharacteristic
noncomputable section
set_option maxHeartbeats 1500000
namespace WP.PositiveConvolution
open Set
lemma universalV_analytic_disk (P:PsiTheory):
    AnalyticOnNhd ℂ (universalV P) (Metric.ball 0 xCritical):=by
  intro z hz
  change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z
  simpa only[iteratedDeriv_eq_iterate] using
    (Phi_analyticAt_open_disk P 0 z (by simpa only[Metric.mem_ball,dist_zero_right] using hz)).iterated_deriv 3
lemma universalV_positive_real (P:PsiTheory) (x:ℝ) (hx:x∈Ico 0 xCritical):
    0<(universalV P x).re ∧ (universalV P x).im=0:=by
  have he:=planarThird_ofReal P x hx
  change universalV P x=Complex.ofReal ((a (inverseY x))⁻¹) at he
  rw[he,Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨inv_pos.mpr (a_pos _ (inverseY_branch x hx).1),rfl⟩
lemma universalV_first_coefficient (P:PsiTheory):WP.coeff (universalV P) 1=1:=by
  simp only[WP.coeff,iteratedDeriv_one,universalV_deriv_zero,Nat.factorial_one,Nat.cast_one,div_one]
lemma universalV_gaussian_point_bound (P:PsiTheory) (x B:ℝ)
    (hx:x∈Ioo 0 xCritical) (hB:0<B) (hVB:(universalV P x).re≤B)
    (θ:ℝ) (hθ:|θ|≤Real.pi) (H:ℕ):
    ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H ≤
      Real.exp (-((2/(B^2*Real.pi^2))*(H:ℝ)*x)*θ^2):=by
  let z:ℂ:=(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  let M:ℝ:=(universalV P x).re
  have hM:0<M:=(universalV_positive_real P x ⟨hx.1.le,hx.2⟩).1
  have hMi:(universalV P x).im=0:=(universalV_positive_real P x ⟨hx.1.le,hx.2⟩).2
  have ha(n:ℕ):0≤realCoeff (universalV P) n:=(universalV_positiveJets P).coefficient_nonneg n |>.1
  have he(n:ℕ):WP.coeff (universalV P) n=Complex.ofReal (realCoeff (universalV P) n):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using (universalV_positiveJets P).coefficient_nonneg n |>.2
  have hz:‖z‖=x:=by simp only[z,norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
  have hhas(w:ℂ)(hw:‖w‖<xCritical):
      HasSum (fun n=>Complex.ofReal (realCoeff (universalV P) n)*w^n) (universalV P w):=by
    simpa only[he] using analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
      (fun w hw=>universalV_analytic_disk P w (by simpa only[Metric.mem_ball,dist_zero_right] using hw)) w hw
  have hr:HasSum (fun n=>realCoeff (universalV P) n*x^n) M:=by
    have hh:=Complex.reCLM.hasSum (hhas (x:ℂ) (by rw[Complex.norm_of_nonneg hx.1.le];exact hx.2))
    change HasSum (fun n=>(Complex.ofReal (realCoeff (universalV P) n)*(x:ℂ)^n).re) M at hh
    simpa only[←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re] using hh
  have h0:realCoeff (universalV P) 0=1:=by simp[realCoeff,WP.coeff,universalV_zero]
  have h1:realCoeff (universalV P) 1=1:=by simp only[realCoeff,universalV_first_coefficient,Complex.one_re]
  have hbound:=positive_series_character_exp_bound _ x hx.1.le ha z (universalV P z) M hM hz
    (hhas z (hz.trans_lt hx.2)) hr
  have hzre:z.re=x*Real.cos θ:=by simp only[z,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]
  rw[h0,h1,one_mul,hzre,show x-x*Real.cos θ=x*(1-Real.cos θ) by ring] at hbound
  simp only[one_mul] at hbound
  have hMnorm:‖universalV P x‖=M:=by
    have heq:universalV P x=Complex.ofReal M:=by
      apply Complex.ext
      · rfl
      · simpa only[Complex.ofReal_im] using hMi
    rw[heq,Complex.norm_of_nonneg hM.le]
  have hcos:2/Real.pi^2*θ^2≤1-Real.cos θ:=by linarith[Real.cos_le_one_sub_mul_cos_sq hθ]
  have hvar:2/(B^2*Real.pi^2)*x*θ^2≤x*(1-Real.cos θ)/M^2:=by
    calc
      _ = x*(2/Real.pi^2*θ^2)/B^2:=by field_simp <;>ring
      _ ≤ x*(1-Real.cos θ)/B^2:=div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcos hx.1.le) (sq_nonneg _)
      _ ≤ _:=div_le_div_of_nonneg_left (mul_nonneg hx.1.le (sub_nonneg.mpr (Real.cos_le_one _)))
        (sq_pos_of_pos hM) (sq_le_sq₀ hM.le hB.le |>.mpr hVB)
  have hb:‖universalV P z/universalV P x‖≤Real.exp (-(2/(B^2*Real.pi^2)*x*θ^2)):=by
    rw[norm_div,hMnorm]
    exact hbound.trans (Real.exp_le_exp.mpr (neg_le_neg hvar))
  have hp:=pow_le_pow_left₀ (norm_nonneg _) hb H
  rw[←Real.exp_nat_mul] at hp
  convert hp using 1 <;>ring
end WP.PositiveConvolution
namespace WP.PositiveConvolution
open Set
lemma compact_parameter_upper_bounds (P:PsiTheory) (b:ℝ) (hb:0≤b) (hbx:b<xCritical):
    ∃B K:ℝ,0<B∧0<K∧∀x∈Icc 0 b,
      (universalV P x).re≤B ∧ deriv Psi x≤K:=by
  have hV:ContinuousOn (fun x:ℝ=>(universalV P x).re) (Icc 0 b):=by
    intro x hx
    have ha:=universalV_analytic_disk P (x:ℂ)
      (by simpa only[Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hx.1] using hx.2.trans_lt hbx)
    exact (Complex.continuous_re.continuousAt.comp (ha.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hD:ContinuousOn (deriv Psi) (Icc 0 b):=by
    intro x hx
    exact (Analysis.Psi_analyticAt_interior x ⟨hx.1,hx.2.trans_lt hbx⟩).deriv.continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩:=isCompact_Icc.exists_bound_of_continuousOn hV
  obtain ⟨K,hK⟩:=isCompact_Icc.exists_bound_of_continuousOn hD
  refine ⟨max 1 B,max 1 K,lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact ⟨(le_abs_self _).trans ((hB x hx).trans (le_max_right _ _)),
    (le_abs_self _).trans ((hK x hx).trans (le_max_right _ _))⟩
end WP.PositiveConvolution
