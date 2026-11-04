import WPFormalization.Analysis.KKernelPositivity
import WPFormalization.Analysis.CoefficientScaling
import WPFormalization.Analysis.RealBessel
/-! Closed-parameter nonnegativity of the actual normalized K inverse
coefficients. Positive parameter Taylor coefficients from Lemma 2.2 are summed
on the genuine zero-free parameter disk, then rescaled by the actual first
root r(Y). The critical branch is the exact linear-kernel coefficient formula.
No uniform moment estimate, higher-root weight, or new paper assumption is used. -/
noncomputable section
namespace WP.Analysis
lemma kInverseCoeff_hasSum (m : ℕ) (Y : ℂ) (hY : ‖Y‖ < y₀) :
    HasSum (fun q => WP.coeff (kInverseCoeff m) q*Y^q) (kInverseCoeff m Y) := by
  have hf : DifferentiableOn ℂ (kInverseCoeff m) (Metric.ball 0 y₀) := by
    intro W hW
    apply DifferentiableAt.differentiableWithinAt
    exact (kInverseCoeff_analyticAt m W (derivX_ne_zero_of_norm_lt W (by simpa using hW))).differentiableAt
  have hs := Complex.hasSum_taylorSeries_on_ball hf (by simpa using hY)
  convert hs using 1
  ext q
  simp only [WP.coeff,sub_zero,smul_eq_mul]
  ring
lemma kInverseCoeff_real_hasSum (m : ℕ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    HasSum (fun q => realCoeff (kInverseCoeff m) q*Y^q) (kInverseCoeff m Y).re := by
  have hn : ‖(Y : ℂ)‖ < y₀ := by simpa [abs_of_nonneg hY.1] using hY.2
  have hs := Complex.reCLM.hasSum (kInverseCoeff_hasSum m Y hn)
  convert hs using 1
  · ext q
    change realCoeff (kInverseCoeff m) q*Y^q = (WP.coeff (kInverseCoeff m) q*(Y : ℂ)^q).re
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]
  · rfl
lemma kInverseCoeff_real_nonneg (m : ℕ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    0 ≤ (kInverseCoeff m Y).re := by
  have hs := kInverseCoeff_real_hasSum m Y hY
  rw [← hs.tsum_eq]
  apply tsum_nonneg
  intro q
  have hc : 0 ≤ realCoeff (kInverseCoeff m) q := by
    simpa only [realTaylor_coeff] using K_kernel_parameter_nonneg.2 q m
  exact mul_nonneg hc (pow_nonneg hY.1 q)
end WP.Analysis
namespace WP
open Analysis
lemma theta_rescaled_kInverse (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (l : ℕ) :
    theta Y l = (r Y)^l*(kInverseCoeff l Y).re := by
  have he : (fun w : ℂ => (barK Y w)⁻¹) =
      fun w : ℂ => (a Y : ℂ)*(K Y ((r Y : ℂ)*w))⁻¹ := by
    funext w
    simp [barK,ne_of_lt hY.2,div_eq_mul_inv]
  have hk : (kInverseCoeff l Y).re = a Y*realCoeff (fun z => (K Y z)⁻¹) l := by
    unfold kInverseCoeff
    rw [derivX_ofReal]
    simp [Complex.mul_re,realCoeff]
  unfold theta
  rw [he,realCoeff_const_mul]
  rw [realCoeff_comp_mul_left (fun z : ℂ => (K Y z)⁻¹) (r Y) l,hk]
  ring
lemma theta_nonneg (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (l : ℕ) : 0 ≤ theta Y l := by
  by_cases he : Y=y₀
  · subst Y
    rw [critical_kernels.2 l]
    norm_num
  · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
    rw [theta_rescaled_kInverse Y hi l]
    exact mul_nonneg (pow_nonneg (r_pos Y hi).le l) (kInverseCoeff_real_nonneg l Y hi)
end WP
