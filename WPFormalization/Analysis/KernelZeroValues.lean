import WPFormalization.Analysis.StationaryIntegral

/-! Exact zero-parameter kernel values and the Sonine integral identity,
proved from the actual entire Taylor series and the exact sine identity.
No asymptotic or external Bessel input is used.
-/
noncomputable section
namespace WP
open MeasureTheory Set Filter
open scoped Topology
lemma H_zero_eq_K_deriv (z : ℂ) : H 0 z = -3*deriv (K 0) z := by
  have hsH := Complex.hasSum_taylorSeries_of_entire (H_differentiable 0) 0 z
  have hsK := (Complex.hasSum_taylorSeries_of_entire (K_differentiable 0).deriv 0 z).mul_left (-3)
  apply HasSum.unique hsH
  convert hsK using 1
  ext n
  simp only [sub_zero,smul_eq_mul]
  rw [← iteratedDeriv_succ',iteratedDeriv_K_zero,iteratedDeriv_H_zero,
    iteratedDeriv_X_succ_zero,iteratedDeriv_X_succ_zero]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : ((n+1).factorial : ℂ) ≠ 0 := by exact_mod_cast (n+1).factorial_ne_zero
  have ho : (oddFactorial (n+1) : ℂ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero (n+1)
  field_simp [hn,hn1,ho]
  rw [pow_succ]
  ring
lemma K_zero_sine_derivative (t : ℂ) :
    K 0 (t^2/2)+t^2*deriv (K 0) (t^2/2) = Complex.cos t := by
  have he : (fun w : ℂ => w*K 0 (w^2/2)) = Complex.sin := by
    funext w
    exact Analysis.rootKernel_sine w
  have hd : HasDerivAt (fun w : ℂ => w*K 0 (w^2/2))
      (K 0 (t^2/2)+t^2*deriv (K 0) (t^2/2)) t := by
    convert (hasDerivAt_id t).mul ((K_differentiable 0 _).hasDerivAt.comp t
      (((hasDerivAt_id t).pow 2).div_const 2)) using 1
    · rfl
    · dsimp; ring
  rw [he] at hd
  exact hd.unique (Complex.hasDerivAt_sin t)
lemma H_zero_pi_value : H 0 ((Real.pi^2/2 : ℝ) : ℂ) = 3/(Real.pi : ℂ)^2 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs := Analysis.rootKernel_sine (Real.pi : ℂ)
  have hsin : Complex.sin (Real.pi : ℂ) = 0 := by rw [← Complex.ofReal_sin,Real.sin_pi,Complex.ofReal_zero]
  rw [hsin] at hs
  have hzero := (mul_eq_zero.mp hs).resolve_left hp
  change K 0 ((Real.pi : ℂ)^2/2) = 0 at hzero
  have hd := K_zero_sine_derivative (Real.pi : ℂ)
  rw [hzero] at hd
  have hcos : Complex.cos (Real.pi : ℂ) = -1 := by rw [← Complex.ofReal_cos,Real.cos_pi]; norm_num
  rw [hcos,zero_add] at hd
  rw [H_zero_eq_K_deriv]
  have he : ((Real.pi^2/2 : ℝ) : ℂ) = (Real.pi : ℂ)^2/2 := by push_cast; rfl
  rw [he]
  apply (eq_div_iff (pow_ne_zero 2 hp)).mpr
  linear_combination -3*hd
lemma sqrt_pi_sq_quarter : Real.sqrt (Real.pi^2/4) = Real.pi/2 := by
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos Real.pi_pos]
  norm_num

lemma sonine_stationary_zero (T : ℝ) (hT : 0 < T) :
    (∫ v in (0 : ℝ)..T,a v/Real.sqrt (T-v)) = Real.sin (2*Real.sqrt T) := by
  rw [stationary_integral_kernel 0 T hT,sub_zero]
  let t := 2*Real.sqrt T
  have hz : (t : ℂ)^2/2 = ((2*T : ℝ) : ℂ) := by
    dsimp [t]
    push_cast
    have hs : ((Real.sqrt T : ℝ) : ℂ)^2 = (T : ℂ) := by exact_mod_cast Real.sq_sqrt hT.le
    rw [mul_pow,hs]
    ring
  have hs := Analysis.rootKernel_sine (t : ℂ)
  rw [hz] at hs
  have hre := congrArg Complex.re hs
  have he : Complex.sin (t : ℂ) = (Real.sin t : ℂ) := (Complex.ofReal_sin t).symm
  rw [he] at hre
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hre
  exact hre


end WP
