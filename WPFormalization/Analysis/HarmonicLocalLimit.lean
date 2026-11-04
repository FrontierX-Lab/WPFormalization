import WPFormalization.Analysis.HarmonicFourierScaling
import WPFormalization.Analysis.GaussianFourier
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicSumMass_scaled_gaussian_error : ∃a:ℕ→ℝ,(∀h,0≤a h) ∧ Tendsto a atTop (𝓝 0) ∧
    ∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,0<h→∀m:ℕ,
      Real.sqrt (h:ℝ)*|harmonicSumMass Y h m-
        Real.exp (-((m:ℝ)-3*(h:ℝ)/2)^2/(2*(h:ℝ)*harmonicVariance Y))/
          Real.sqrt (2*Real.pi*(h:ℝ)*harmonicVariance Y)|≤a h/(2*Real.pi) := by
  obtain ⟨a,ha,ht,herror⟩ := harmonicFourier_uniform_l1_error
  refine ⟨a,ha,ht,?_⟩
  intro Y hY h hh m
  let r := Real.sqrt (h:ℝ)
  let d := (m:ℝ)-3*(h:ℝ)/2
  let q := d/r
  let v := harmonicVariance Y
  let g := Real.exp (-d^2/(2*(h:ℝ)*v))/Real.sqrt (2*Real.pi*(h:ℝ)*v)
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hv : 0<v := harmonicVariance_pos Y hY
  have hp : 0<2*Real.pi := by positivity
  have hMass := harmonicSumMass_scaled_fourier Y hY h m hh
  change (r:ℂ)*(harmonicSumMass Y h m:ℂ)=((2*Real.pi:ℝ):ℂ)⁻¹*
    (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledHarmonicFourier Y h t) at hMass
  have hGauss := gaussian_fourier_normalized v q hv
  change ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*harmonicGaussianKernel Y t)=
    ((Real.exp (-q^2/(2*v))/Real.sqrt (2*Real.pi*v):ℝ):ℂ) at hGauss
  have hScale := gaussian_mass_scaling v d hv h hh
  change r*g=Real.exp (-q^2/(2*v))/Real.sqrt (2*Real.pi*v) at hScale
  have hGScaled : (r:ℂ)*(g:ℂ)=((2*Real.pi:ℝ):ℂ)⁻¹*
      (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*harmonicGaussianKernel Y t) := by
    rw [←Complex.ofReal_mul,hScale]
    exact hGauss.symm
  have hIC := real_fourier_phase_mul_integrable q _ (scaledHarmonicFourier_integrable Y hY h)
  have hIG := real_fourier_phase_mul_integrable q _ (harmonicGaussianKernel_integrable Y hY)
  have hSub : (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)) =
      (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledHarmonicFourier Y h t)-
        (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*harmonicGaussianKernel Y t) := by
    rw [←integral_sub hIC hIG]
    apply integral_congr_ae
    exact ae_of_all _ (fun t=>by simp only [Pi.sub_apply]; ring)
  have hDiff : (r:ℂ)*((harmonicSumMass Y h m-g:ℝ):ℂ)=((2*Real.pi:ℝ):ℂ)⁻¹*
      (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)) := by
    rw [Complex.ofReal_sub,mul_sub,hMass,hGScaled,hSub,mul_sub]
  have hErr := herror Y hY h hh q
  change r*|harmonicSumMass Y h m-g|≤a h/(2*Real.pi)
  calc r*|harmonicSumMass Y h m-g| = ‖(r:ℂ)*((harmonicSumMass Y h m-g:ℝ):ℂ)‖ := by
          rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,Complex.norm_real,Real.norm_eq_abs]
       _ = ‖((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t))‖ := congrArg norm hDiff
       _ = (2*Real.pi)⁻¹*‖∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)‖ := by
          rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
       _ ≤ (2*Real.pi)⁻¹*a h := mul_le_mul_of_nonneg_left hErr (by positivity)
       _ = a h/(2*Real.pi) := by ring
end WP.Analysis

namespace WP
open MeasureTheory Filter Set Complex
open scoped Topology
/- Eq.2.9. Epsilon quantification makes the little-o uniform in Y and central m. -/
/- Blueprint label(s): eq:P13
Paper v3: 2.9 [PDF 18]
Status: CONDITIONALLY_PROVED (Bessel real-zero and classical Pringsheim inputs)
-/
@[blueprint "eq:P13"]
theorem harmonic_local_limit (L : ℝ) (hL : 0 ≤ L) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℕ, ∀ h ≥ h₀, 0 < h →
    ∀ Y ∈ Set.Icc 0 y₀, ∀ m : ℕ, |(m : ℝ)-3*(h : ℝ)/2| ≤ L*Real.sqrt h →
      |harmonicSumMass Y h m -
        Real.exp (-((m : ℝ)-3*(h : ℝ)/2)^2/(2*h*harmonicVariance Y)) /
          Real.sqrt (2*Real.pi*h*harmonicVariance Y)| ≤ ε / Real.sqrt h := by
  intro ε hε
  obtain ⟨a,ha,ht,herror⟩ := Analysis.harmonicSumMass_scaled_gaussian_error
  have hp : 0<2*Real.pi := by positivity
  have hev := ht.eventually (gt_mem_nhds (mul_pos hp hε))
  obtain ⟨h₀,hh₀⟩ := eventually_atTop.mp hev
  refine ⟨h₀,?_⟩
  intro h hhh hh Y hY m hm
  have hr : 0<Real.sqrt (h:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hErr := herror Y hY h hh m
  apply (le_div_iff₀ hr).mpr
  have hE : a h/(2*Real.pi)≤ε := (div_le_iff₀ hp).mpr (by nlinarith [hh₀ h hhh])
  nlinarith

end WP
