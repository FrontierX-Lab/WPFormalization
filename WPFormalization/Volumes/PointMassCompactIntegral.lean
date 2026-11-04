import WPFormalization.Volumes.PointMassCompact
import WPFormalization.Analysis.PointMassIntegrals

noncomputable section
namespace WP.PositiveConvolution
open Set MeasureTheory
lemma universalV_circle_continuous (P:PsiTheory) (x:ℝ) (hx:x∈Ioo 0 xCritical):
    Continuous (fun θ:ℝ=>universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))):=by
  rw[continuous_iff_continuousAt]
  intro θ
  have hn:‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖<xCritical:=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact hx.2
  exact (universalV_analytic_disk P _ (by simpa only[Metric.mem_ball,dist_zero_right] using hn)).continuousAt.comp
    (by fun_prop)
lemma compact_character_integral_scaled_bound (P:PsiTheory) (c₀ b:ℝ) (hc:0<c₀)
    (hb:0<b) (hbx:b<xCritical):
    ∃C:ℝ,0<C∧∀h H:ℕ,1≤h→1≤H→c₀*(h:ℝ)≤H→∀x∈Ioc 0 b,
      (∫θ:ℝ in (-Real.pi)..Real.pi,
        ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H)*
          Real.sqrt ((h:ℝ)*euler Psi x)≤C:=by
  obtain ⟨B,K,hB,hK,hpars⟩:=compact_parameter_upper_bounds P b hb.le hbx
  let κ:ℝ:=2/(B^2*Real.pi^2)
  have hκ:0<κ:=by dsimp[κ];positivity
  refine ⟨Real.sqrt (Real.pi*(K/c₀)/κ),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro h H hh hH hrel x hx
  have hxi:x∈Ioo 0 xCritical:=⟨hx.1,hx.2.trans_lt hbx⟩
  have hHp:0<(H:ℝ):=by exact_mod_cast (show 0<H by omega)
  have ht:0<(H:ℝ)*x:=mul_pos hHp hx.1
  have hk:0<κ*((H:ℝ)*x):=mul_pos hκ ht
  have hcf:Continuous (fun θ:ℝ=>
      ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H):=
    (((universalV_circle_continuous P x hxi).div_const _).norm.pow H)
  have hi:=intervalIntegral.integral_mono_on (μ:=volume)
    (by linarith[Real.pi_pos]:-Real.pi≤Real.pi) (hcf.intervalIntegrable _ _)
    ((by fun_prop:Continuous (fun θ:ℝ=>Real.exp (-(κ*((H:ℝ)*x))*θ^2))).intervalIntegrable _ _)
    (fun θ hθ=>by
      have hθ':|θ|≤Real.pi:=abs_le.mpr hθ
      simpa only[κ,mul_assoc] using universalV_gaussian_point_bound P x B hxi hB
        (hpars x ⟨hx.1.le,hx.2⟩).1 θ hθ' H)
  have hgauss:=hi.trans (gaussian_circle_integral_bound (κ*((H:ℝ)*x)) hk)
  have hvar:euler Psi x≤K*x:=by
    have hd:deriv Psi x≤K:=(hpars x ⟨hx.1.le,hx.2⟩).2
    dsimp only[euler]
    nlinarith[mul_le_mul_of_nonneg_left hd hx.1.le]
  have hrat:(h:ℝ)≤(H:ℝ)/c₀:=(le_div_iff₀ hc).mpr (by simpa only[mul_comm] using hrel)
  have hv:(h:ℝ)*euler Psi x≤K/c₀*((H:ℝ)*x):=by
    calc
      _ ≤ (h:ℝ)*(K*x):=mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg _)
      _ ≤ ((H:ℝ)/c₀)*(K*x):=mul_le_mul_of_nonneg_right hrat (mul_nonneg hK.le hx.1.le)
      _ = _:=by ring
  have he:Real.sqrt (Real.pi/(κ*((H:ℝ)*x)))*Real.sqrt (K/c₀*((H:ℝ)*x))=
      Real.sqrt (Real.pi*(K/c₀)/κ):=by
    rw[←Real.sqrt_mul (by positivity)]
    congr 1
    field_simp [hx.1.ne',hκ.ne',hHp.ne',hc.ne']
  exact (mul_le_mul hgauss (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq he
end WP.PositiveConvolution
