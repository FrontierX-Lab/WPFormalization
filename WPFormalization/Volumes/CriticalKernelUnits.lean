import WPFormalization.Volumes.CriticalPuiseux
import WPFormalization.Analysis.KernelMomentComplexification
import WPFormalization.Marked.VolumeRatios
/-! Analytic unit factors of the actual A, a, and first-root r near the critical endpoint.
The physical identities and all critical values are derived from the existing common
holomorphic kernel family and the genuine X jets. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
structure CriticalKernelUnits where
  A : ℂ → ℂ
  a₁ : ℂ → ℂ
  r₁ : ℂ → ℂ
  A_analytic : AnalyticAt ℂ A 0
  a_analytic : AnalyticAt ℂ a₁ 0
  r_analytic : AnalyticAt ℂ r₁ 0
  A_zero : A 0=(2/15:ℂ)
  a_zero : a₁ 0=(criticalB:ℂ)
  r_zero : r₁ 0=3
  physical : ∀ᶠ δ : ℝ in 𝓝 0, 0 < δ → δ < y₀ ∧
    A (δ:ℂ)=(WP.A (y₀-δ):ℂ) ∧
    (WP.a (y₀-δ):ℂ)=(δ:ℂ)*a₁ (δ:ℂ) ∧
    (WP.r (y₀-δ):ℂ)=(δ:ℂ)*r₁ (δ:ℂ)

lemma exists_criticalKernelUnits : Nonempty CriticalKernelUnits := by
  obtain ⟨Ω,hΩ,hΩconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ := common_holomorphic_kernel_moments
  have hcrit : (y₀:ℂ) ∈ Ω := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  let Aδ : ℂ → ℂ := fun δ => Ahat ((y₀:ℂ)-δ)
  let aδ : ℂ → ℂ := fun δ => deriv X ((y₀:ℂ)-δ)
  let rδ : ℂ → ℂ := fun δ => R ((y₀:ℂ)-δ)
  have hAδ : AnalyticAt ℂ Aδ 0 := by
    have hAa : AnalyticAt ℂ Ahat ((y₀:ℂ)-(0:ℂ)) := by simpa only [sub_zero] using hA _ hcrit
    exact hAa.comp (analyticAt_const.sub analyticAt_id)
  have haδ : AnalyticAt ℂ aδ 0 := ((X_differentiable.analyticAt _).deriv).comp (analyticAt_const.sub analyticAt_id)
  have hrδ : AnalyticAt ℂ rδ 0 := by
    have hRa : AnalyticAt ℂ R ((y₀:ℂ)-(0:ℂ)) := by simpa only [sub_zero] using hR _ hcrit
    exact hRa.comp (analyticAt_const.sub analyticAt_id)
  have ha0 : aδ 0=0 := by simp only [aδ,sub_zero,derivX_y₀_zero]
  have hr0 : rδ 0=0 := by simpa only [rδ,sub_zero] using hR0
  have hshift : HasDerivAt (fun δ : ℂ => (y₀:ℂ)-δ) (-1) 0 := by
    convert! (hasDerivAt_const (0:ℂ) (y₀:ℂ)).sub (hasDerivAt_id (0:ℂ)) using 1 <;> simp
  have haD : deriv aδ 0=(criticalB:ℂ) := by
    have hXa : HasDerivAt (deriv X) (iteratedDeriv 2 X (y₀:ℂ)) ((y₀:ℂ)-(0:ℂ)) := by
      convert! ((X_differentiable.analyticAt (y₀:ℂ)).deriv).differentiableAt.hasDerivAt using 1 <;>
        simp only [sub_zero,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    have hd := hXa.comp 0 hshift
    convert! hd.deriv using 1
    rw [X_second_critical_value]
    simp
  have hrD : deriv rδ 0=3 := by
    have hRa : HasDerivAt R (-3) ((y₀:ℂ)-(0:ℂ)) := by
      simpa only [sub_zero,hR'] using (hR _ hcrit).differentiableAt.hasDerivAt
    have hd := hRa.comp 0 hshift
    convert! hd.deriv using 1 <;> norm_num
  obtain ⟨a₁,ha₁,ha₁0,haF⟩ := complex_analytic_linear_factor aδ haδ ha0
  obtain ⟨r₁,hr₁,hr₁0,hrF⟩ := complex_analytic_linear_factor rδ hrδ hr0
  have hA0 : Aδ 0=(2/15:ℂ) := by
    dsimp only [Aδ]
    rw [sub_zero,(hmatch y₀ ⟨y₀_pos.le,le_rfl⟩).2]
    norm_num [WP.A,barH]
  refine ⟨⟨Aδ,a₁,r₁,hAδ,ha₁,hr₁,hA0,ha₁0.trans haD,hr₁0.trans hrD,?_⟩⟩
  have hcast : Tendsto (fun δ : ℝ => (δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto
  filter_upwards [hcast.eventually haF,hcast.eventually hrF,eventually_lt_nhds y₀_pos] with δ hfa hfr hδlt hδ
  have hY : y₀-δ ∈ Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  have hYc : y₀-δ ∈ Icc (0:ℝ) y₀ := ⟨hY.1,hY.2.le⟩
  refine ⟨hδlt,?_,?_,?_⟩
  · dsimp only [Aδ]
    rw [←Complex.ofReal_sub,(hmatch _ hYc).2]
  · dsimp only [aδ] at hfa
    rw [←Complex.ofReal_sub,derivX_ofReal] at hfa
    exact hfa
  · dsimp only [rδ] at hfr
    rw [←Complex.ofReal_sub,hraw _ hY] at hfr
    exact hfr
end WP.Analysis
