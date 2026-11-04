import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.CauchyIntegral

/-! A real continuous implicit branch is analytic when its defining complex
equation is C¹ and the complex transverse derivative is invertible. Mathlib's
C¹ implicit-function theorem gives a one-complex-variable branch; Cauchy's
theorem makes it analytic. Restriction to the real axis and local uniqueness
identify the given actual branch. No existence, continuity or root-selection
property of a paper-specific family is assumed here.
-/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology ContDiff
lemma analyticAt_real_implicit_continuous_branch
    (F : ℂ × ℂ → ℂ) (b : ℝ → ℝ) (x₀ : ℝ)
    (hF : ContDiffAt ℂ 1 F ((x₀ : ℂ),(b x₀ : ℂ)))
    (hInv : (fderiv ℂ F ((x₀ : ℂ),(b x₀ : ℂ)) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible)
    (hb : ContinuousAt b x₀)
    (hEq : ∀ᶠ x : ℝ in 𝓝 x₀,F ((x : ℂ),(b x : ℂ)) = F ((x₀ : ℂ),(b x₀ : ℂ))) :
    AnalyticAt ℝ b x₀ := by
  have hn : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let ψ := hF.implicitFunction hn hInv
  have hcψ : ContDiffAt ℂ 1 ψ (x₀ : ℂ) := hF.contDiffAt_implicitFunction hn hInv
  have haψ : AnalyticAt ℂ ψ (x₀ : ℂ) := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hcψ.eventually (by norm_num)] with z hz
    exact hz.differentiableAt (by norm_num)
  have haψR : AnalyticAt ℝ ψ (x₀ : ℂ) := haψ.restrictScalars
  have hcomp : AnalyticAt ℝ (fun x : ℝ => ψ (x : ℂ)) x₀ :=
    haψR.comp (Complex.ofRealCLM.analyticAt x₀)
  have hreal : AnalyticAt ℝ (fun x : ℝ => (ψ (x : ℂ)).re) x₀ :=
    (Complex.reCLM.analyticAt _).comp hcomp
  have he := hF.eventually_apply_eq_iff_implicitFunction hn hInv
  have hg : Tendsto (fun x : ℝ => ((x : ℂ),(b x : ℂ))) (𝓝 x₀)
      (𝓝 ((x₀ : ℂ),(b x₀ : ℂ))) := by
    exact (Complex.continuous_ofReal.continuousAt).prodMk
      (Complex.continuous_ofReal.continuousAt.comp hb)
  apply hreal.congr
  filter_upwards [hg.eventually he,hEq] with x hx hFx
  have hp := hx.mp hFx
  change (ψ (x : ℂ)).re = b x
  change ψ (x : ℂ) = (b x : ℂ) at hp
  rw [hp,Complex.ofReal_re]

lemma complex_clm_isInvertible_of_apply_one_ne_zero (L : ℂ →L[ℂ] ℂ) (h : L 1 ≠ 0) :
    L.IsInvertible := by
  have he (z : ℂ) : L z = (L 1)*z := by
    simpa only [smul_eq_mul,mul_one,mul_comm] using L.map_smul z (1 : ℂ)
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
  · apply ContinuousLinearMap.ext
    intro z
    change L ((L 1)⁻¹*z) = z
    rw [he ((L 1)⁻¹*z)]
    field_simp [h]
  · apply ContinuousLinearMap.ext
    intro z
    change (L 1)⁻¹*L z = z
    rw [he z]
    field_simp [h]


/- Composing an actual real implicit branch with another complex C¹ map
preserves real analyticity; the local complex branch and uniqueness supply
the proof without a separate multivariable analytic integration interface. -/
lemma analyticAt_real_implicit_comp
    (F H : ℂ × ℂ → ℂ) (b : ℝ → ℝ) (x₀ : ℝ)
    (hF : ContDiffAt ℂ 1 F ((x₀ : ℂ),(b x₀ : ℂ)))
    (hH : ContDiffAt ℂ 1 H ((x₀ : ℂ),(b x₀ : ℂ)))
    (hInv : (fderiv ℂ F ((x₀ : ℂ),(b x₀ : ℂ)) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible)
    (hb : ContinuousAt b x₀)
    (hEq : ∀ᶠ x : ℝ in 𝓝 x₀,F ((x : ℂ),(b x : ℂ)) = F ((x₀ : ℂ),(b x₀ : ℂ))) :
    AnalyticAt ℝ (fun x : ℝ => (H ((x:ℂ),(b x:ℂ))).re) x₀ := by
  have hn : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let ψ := hF.implicitFunction hn hInv
  have hcψ : ContDiffAt ℂ 1 ψ (x₀ : ℂ) := hF.contDiffAt_implicitFunction hn hInv
  have hψ : ψ (x₀:ℂ) = (b x₀:ℂ) := hF.implicitFunction_apply_self hn hInv
  have hG : ContDiffAt ℂ 1 (fun z : ℂ => H (z,ψ z)) (x₀:ℂ) := by
    have hH' : ContDiffAt ℂ 1 H ((x₀:ℂ),ψ (x₀:ℂ)) := by simpa only [hψ] using hH
    exact hH'.comp (x₀:ℂ) (contDiffAt_id.prodMk hcψ)
  have ha : AnalyticAt ℂ (fun z : ℂ => H (z,ψ z)) (x₀:ℂ) := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hG.eventually (by norm_num)] with z hz
    exact hz.differentiableAt (by norm_num)
  have hc : AnalyticAt ℝ (fun x : ℝ => H ((x:ℂ),ψ (x:ℂ))) x₀ :=
    ha.restrictScalars.comp (Complex.ofRealCLM.analyticAt x₀)
  have hr : AnalyticAt ℝ (fun x : ℝ => (H ((x:ℂ),ψ (x:ℂ))).re) x₀ :=
    (Complex.reCLM.analyticAt _).comp hc
  have he := hF.eventually_apply_eq_iff_implicitFunction hn hInv
  have hg : Tendsto (fun x : ℝ => ((x : ℂ),(b x : ℂ))) (𝓝 x₀)
      (𝓝 ((x₀ : ℂ),(b x₀ : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.prodMk
      (Complex.continuous_ofReal.continuousAt.comp hb)
  apply hr.congr
  filter_upwards [hg.eventually he,hEq] with x hx hFx
  have hp := hx.mp hFx
  change ψ (x : ℂ) = (b x : ℂ) at hp
  rw [hp]

end WP.Analysis
