import WPFormalization.Statements.Basic

/-! An explicit lower bound for sine on the half-integer pi circles used
in the actual kernel zero argument. This is proved from the real sine
Lipschitz bound and the exact real/imaginary norm identity. -/
noncomputable section
namespace WP.Analysis
open Set
open scoped Topology
lemma complex_sin_coordinates (z : ℂ) :
    Complex.sin z = ((Real.sin z.re*Real.cosh z.im:ℝ):ℂ)+
      ((Real.cos z.re*Real.sinh z.im:ℝ):ℂ)*Complex.I := by
  conv_lhs => rw [← Complex.re_add_im z,Complex.sin_add,Complex.cos_mul_I,Complex.sin_mul_I]
  rw [← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_cosh,← Complex.ofReal_sinh]
  push_cast
  ring
lemma norm_complex_sin_sq (z : ℂ) :
    ‖Complex.sin z‖^2 = (Real.sin z.re)^2+(Real.sinh z.im)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply,complex_sin_coordinates]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,
    Complex.I_im,mul_zero,sub_zero,add_zero,Complex.add_im,Complex.mul_im,mul_one]
  linear_combination (Real.sin z.re)^2*(Real.cosh_sq_sub_sinh_sq z.im)+
    (Real.sinh z.im)^2*(Real.sin_sq_add_cos_sq z.re)
lemma abs_sin_re_le_norm_sin (z : ℂ) : |Real.sin z.re| ≤ ‖Complex.sin z‖ := by
  have hh := norm_complex_sin_sq z
  nlinarith [sq_abs (Real.sin z.re),sq_nonneg (Real.sinh z.im),norm_nonneg (Complex.sin z),abs_nonneg (Real.sin z.re)]
lemma abs_im_le_norm_sin (z : ℂ) : |z.im| ≤ ‖Complex.sin z‖ := by
  have hh := norm_complex_sin_sq z
  have hS : |Real.sinh z.im| ≤ ‖Complex.sin z‖ := by
    nlinarith [sq_abs (Real.sinh z.im),sq_nonneg (Real.sin z.re),norm_nonneg (Complex.sin z),abs_nonneg (Real.sinh z.im)]
  rw [Real.abs_sinh] at hS
  exact ((Real.self_le_sinh_iff).2 (abs_nonneg z.im)).trans hS
lemma complex_sin_circle_lower (N : ℕ) (z : ℂ)
    (hz : ‖z‖ = ((N:ℝ)+1/2)*Real.pi) : (1/4:ℝ) ≤ ‖Complex.sin z‖ := by
  let R : ℝ := ((N:ℝ)+1/2)*Real.pi
  have hR : ‖z‖ = R := hz
  by_cases hy : (1/4:ℝ) ≤ |z.im|
  · exact hy.trans (abs_im_le_norm_sin z)
  have hy' : |z.im| ≤ (1/4:ℝ) := (lt_of_not_ge hy).le
  have hx : |z.re| ≤ R := by simpa only [hR] using Complex.abs_re_le_norm z
  have ht : R ≤ |z.re|+|z.im| := by
    have hh := norm_add_le (z.re:ℂ) ((z.im:ℂ)*Complex.I)
    simpa only [Complex.re_add_im,Complex.norm_real,Real.norm_eq_abs,norm_mul,
      Complex.norm_I,mul_one,hR] using hh
  have hd : |(|z.re| - R)| ≤ (1/4:ℝ) := by rw [abs_of_nonpos (sub_nonpos.mpr hx)];linarith
  have hsinR : |Real.sin R| = 1 := by
    have he : R = Real.pi/2+(N:ℝ)*Real.pi := by dsimp [R];ring
    rw [he,Real.sin_add_nat_mul_pi]
    simp
  have hLip := Real.abs_sin_sub_sin_le |z.re| R
  have hAbs := abs_sub_abs_le_abs_sub (Real.sin R) (Real.sin (|z.re|))
  have hsinAbs : |Real.sin (|z.re|)| = |Real.sin z.re| := by
    by_cases hr : 0 ≤ z.re
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg (lt_of_not_ge hr),Real.sin_neg,abs_neg]
  rw [hsinR,abs_sub_comm,hsinAbs] at hAbs
  have hb : (3/4:ℝ) ≤ |Real.sin z.re| := by linarith
  exact (by norm_num : (1/4:ℝ) ≤ 3/4).trans (hb.trans (abs_sin_re_le_norm_sin z))
end WP.Analysis
