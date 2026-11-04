import WPFormalization.Analysis.BoundaryFactorMomentCore
import WPFormalization.Volumes.BoundaryTranslationKernel
import WPFormalization.Analysis.FirstKernelRoot

/-! Uniform quadratic moments of the actual boundary translation weights. -/
noncomputable section
namespace WP.Analysis
open Set WP.BoundaryConvolution

lemma boundary_degree_weight_square_moment (r t Y : ℝ) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (hY : 0 ≤ Y) :
    Summable (fun b : ℕ => ((b:ℝ)+1)^2 *
      (r^b/(oddFactorial b:ℝ)*(translationWeight t b (Y:ℂ)).re)) ∧
    (∑' b : ℕ, ((b:ℝ)+1)^2 *
      (r^b/(oddFactorial b:ℝ)*(translationWeight t b (Y:ℂ)).re)) ≤
      Real.exp (t*Y)*Real.exp (4*r*t) := by
  have hs := boundary_weighted_kernel_moment r t Y hr ht hY
    (fun b => (translationKernel b ((t*Y:ℝ):ℂ)).re)
    (fun b => translationKernel_real_hasSum b (t*Y))
  have he (b : ℕ) : (translationWeight t b (Y:ℂ)).re =
      t^b*(translationKernel b ((t*Y:ℝ):ℂ)).re := by
    simp [translationWeight,←Complex.ofReal_pow,Complex.mul_re]
  simpa only [he,mul_assoc] using hs

lemma boundary_degree_weight_moment_uniform (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ Y ∈ Ico 0 y₀, ∀ t ∈ Icc 0 t₀,
      Summable (fun b : ℕ => ((b:ℝ)+1)^2 *
        (r Y^b/(oddFactorial b:ℝ)*(translationWeight t b (Y:ℂ)).re)) ∧
      (∑' b : ℕ, ((b:ℝ)+1)^2 *
        (r Y^b/(oddFactorial b:ℝ)*(translationWeight t b (Y:ℂ)).re)) ≤ M := by
  let R : ℝ := Real.pi^2/2
  have hR : 0 < R := by dsimp [R];positivity
  have hRb : ∀ Y ∈ Ico 0 y₀, r Y ≤ R := by
    intro Y hY
    have H := r_le_pi Y hY
    dsimp [R]
    linarith [hY.1]
  refine ⟨Real.exp (t₀*y₀)*Real.exp (4*R*t₀),by positivity,?_⟩
  intro Y hY t ht
  obtain ⟨hs,hb⟩ := boundary_degree_weight_square_moment (r Y) t Y
    (r_pos Y hY).le ht.1 hY.1
  refine ⟨hs,hb.trans ?_⟩
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul ht.2 hY.2.le hY.1 ht₀))
    (Real.exp_le_exp.mpr (by
      have hm := mul_le_mul (hRb Y hY) ht.2 ht.1 hR.le
      nlinarith)) (Real.exp_pos _).le (Real.exp_pos _).le
end WP.Analysis
