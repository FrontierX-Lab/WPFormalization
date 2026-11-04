import WPFormalization.Analysis.CriticalKernelLipschitz

/-! Joint complex calculus for compact kernel integrals and their root curves.
The simple zero of X' is divided out using Mathlib dslope; its unit is
nonzero on the physical interval. Regularized normalized kernels retain
the actual interior restriction and are holomorphic in the parameter. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma kernel_moment_prod_contDiff_one (q : ℝ → ℂ) (hq : Continuous q) (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) :
    ContDiff ℂ 1 (fun p : ℂ × ℂ => ∫ s : ℝ in (0)..1,
      q s*g (p.1+p.2/2*(1-(s:ℂ)^2))) := by
  let L : ℝ → (ℂ × ℂ →L[ℂ] ℂ) := fun s => ContinuousLinearMap.fst ℂ ℂ ℂ+
    ((1-(s:ℂ)^2)/2) • ContinuousLinearMap.snd ℂ ℂ ℂ
  have hL : Continuous L := by dsimp [L];fun_prop
  have hc := affineIntegral_prod_contDiff_one q (fun _ => 0) L hq continuous_const hL g hg
  convert! hc using 1
  funext p
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [L,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  change q s*g (p.1+p.2/2*(1-(s:ℂ)^2)) = q s*g (0+(p.1+((1-(s:ℂ)^2)/2)*p.2))
  congr 2
  ring

lemma K_prod_contDiff_one : ContDiff ℂ 1 (fun p : ℂ × ℂ => K p.1 p.2) := by
  simpa only [K,one_mul] using
    kernel_moment_prod_contDiff_one (fun _ => 1) continuous_const (deriv X) X_differentiable.deriv

lemma H_prod_contDiff_one : ContDiff ℂ 1 (fun p : ℂ × ℂ => H p.1 p.2) := by
  simpa only [H] using
    contDiff_const.mul (kernel_moment_prod_contDiff_one (fun s => (s:ℂ)^2) (by fun_prop) (deriv X) X_differentiable.deriv)

lemma complex_analyticAt_of_contDiffAt_one (f : ℂ → ℂ) (z : ℂ) (hf : ContDiffAt ℂ 1 f z) :
    AnalyticAt ℂ f z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hf.eventually (by norm_num)] with w hw
  exact hw.differentiableAt (by norm_num)

lemma K_root_curve_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => K z (R z*w)) Ω := by
  intro z hz
  apply complex_analyticAt_of_contDiffAt_one
  have hp : ContDiffAt ℂ 1 (fun ζ : ℂ => (ζ,R ζ*w)) z :=
    contDiffAt_id.prodMk ((hR z hz).contDiffAt.mul contDiffAt_const)
  simpa only [Function.comp_def] using K_prod_contDiff_one.contDiffAt.comp z hp

lemma H_root_curve_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => H z (R z*w)) Ω := by
  intro z hz
  apply complex_analyticAt_of_contDiffAt_one
  have hp : ContDiffAt ℂ 1 (fun ζ : ℂ => (ζ,R ζ*w)) z :=
    contDiffAt_id.prodMk ((hR z hz).contDiffAt.mul contDiffAt_const)
  simpa only [Function.comp_def] using H_prod_contDiff_one.contDiffAt.comp z hp

lemma dslope_analyticOnNhd_complex (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Ω) (c : ℂ) (hc : c ∈ Ω) :
    AnalyticOnNhd ℂ (dslope f c) Ω :=
  ((Complex.differentiableOn_dslope (hΩ.mem_nhds hc)).mpr hf.differentiableOn).analyticOnNhd hΩ

def complexAUnit : ℂ → ℂ := dslope (deriv X) (y₀:ℂ)

lemma complexAUnit_analytic : AnalyticOnNhd ℂ complexAUnit univ := by
  exact dslope_analyticOnNhd_complex univ isOpen_univ (deriv X)
    (fun z _ => X_differentiable.deriv.analyticAt z) y₀ (mem_univ _)

lemma complexAUnit_factor (z : ℂ) : (z-(y₀:ℂ))*complexAUnit z=deriv X z := by
  simpa only [complexAUnit,smul_eq_mul,derivX_y₀_zero,sub_zero] using
    sub_smul_dslope (deriv X) (y₀:ℂ) z

lemma complexAUnit_ne_zero_physical (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) : complexAUnit (Y:ℂ)≠0 := by
  by_cases he : Y=y₀
  · subst Y
    simpa only [complexAUnit,dslope_same,iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using
      iteratedDeriv_two_X_y₀_ne_zero
  · intro hzero
    have hfactor := complexAUnit_factor (Y:ℂ)
    rw [hzero,mul_zero] at hfactor
    have ha : a Y=0 := by
      simpa only [a,Complex.zero_re] using congrArg Complex.re hfactor.symm
    exact (a_pos Y ⟨hY.1,lt_of_le_of_ne hY.2 he⟩).ne' ha

lemma normalized_kernels_tendsto_critical_pointwise (w : ℂ) :
    Tendsto (fun Y : ℝ => barK Y w) (𝓝[<] y₀) (𝓝 (1-w)) ∧
      Tendsto (fun Y : ℝ => barH Y w) (𝓝[<] y₀) (𝓝 (1-(3/5:ℂ)*w)) := by
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hR : 0 < ‖w‖+1 := by positivity
    filter_upwards [critical_normalized_kernels_uniform (‖w‖+1) hR (ε/2) (by positivity)] with Y hY
    rw [dist_eq_norm]
    exact (hY w (by linarith)).1.trans_lt (by linarith)
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hR : 0 < ‖w‖+1 := by positivity
    filter_upwards [critical_normalized_kernels_uniform (‖w‖+1) hR (ε/2) (by positivity)] with Y hY
    rw [dist_eq_norm]
    exact (hY w (by linarith)).2.trans_lt (by linarith)

def regularizedKernel (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (z w : ℂ) : ℂ :=
  dslope (fun ζ => B ζ (R ζ*w)) (y₀:ℂ) z/complexAUnit z

lemma regularizedKernel_analyticOnNhd (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ) ∈ Ω)
    (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB : ∀ w : ℂ,AnalyticOnNhd ℂ (fun z => B z (R z*w)) Ω)
    (hunit : ∀ z ∈ Ω,complexAUnit z≠0) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => regularizedKernel B R z w) Ω := by
  intro z hz
  exact (dslope_analyticOnNhd_complex Ω hΩ _ (hB w) y₀ hc z hz).div
    (complexAUnit_analytic z (mem_univ _)) (hunit z hz)

lemma regularizedKernel_restrict_interior (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB0 : ∀ z : ℂ,B z 0=deriv X z) (hR0 : R (y₀:ℂ)=0)
    (hR : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) (w : ℂ) :
    regularizedKernel B R (Y:ℂ) w=B (Y:ℂ) ((r Y:ℂ)*w)/(a Y:ℂ) := by
  let N : ℂ → ℂ := fun z => B z (R z*w)
  have hN0 : N (y₀:ℂ)=0 := by dsimp [N];rw [hR0,zero_mul,hB0,derivX_y₀_zero]
  have hN := sub_smul_dslope N (y₀:ℂ) (Y:ℂ)
  simp only [smul_eq_mul,hN0,sub_zero] at hN
  have hA := complexAUnit_factor (Y:ℂ)
  rw [derivX_ofReal] at hA
  have ha : (a Y:ℂ)≠0 := by exact_mod_cast (a_pos Y hY).ne'
  change dslope N (y₀:ℂ) (Y:ℂ)/complexAUnit (Y:ℂ)=B (Y:ℂ) ((r Y:ℂ)*w)/(a Y:ℂ)
  apply (div_eq_div_iff (complexAUnit_ne_zero_physical Y ⟨hY.1,hY.2.le⟩) ha).mpr
  rw [←hA]
  calc
    _ = (((Y:ℂ)-(y₀:ℂ))*dslope N (y₀:ℂ) (Y:ℂ))*complexAUnit (Y:ℂ) := by ring
    _ = N (Y:ℂ)*complexAUnit (Y:ℂ) := by rw [hN]
    _ = _ := by dsimp [N];rw [hR Y hY]

end WP.Analysis
