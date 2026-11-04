import WPFormalization.Analysis.KernelSineReference

/-! The undeformed JT density from the actual entire kernel. -/
noncomputable section
namespace WP.JT

/-- The sine identity continued along the imaginary axis.  The identity
includes the removable endpoint q=0 and uses only the existing K kernel. -/
lemma kernel_density_zero_parameter (q : ℝ) (hq : 0 ≤ q) :
    Real.sqrt q / (2 * Real.pi) *
      (K 0 ((-2 * Real.pi^2 * q : ℝ) : ℂ)).re =
      Real.sinh (2 * Real.pi * Real.sqrt q) / (4 * Real.pi^2) := by
  let t : ℝ := 2 * Real.pi * Real.sqrt q
  have hs := Analysis.sineReference_mul ((t : ℂ) * Complex.I)
  have harg : ((t : ℂ) * Complex.I)^2 / 2 = ((-2 * Real.pi^2 * q : ℝ) : ℂ) := by
    dsimp [t]
    push_cast
    rw [mul_pow, Complex.I_sq]
    have hsq : (Real.sqrt q : ℂ)^2 = (q : ℂ) := by
      exact_mod_cast Real.sq_sqrt hq
    ring_nf
    rw [hsq]
  simp only [Analysis.sineReference, harg, Complex.sin_mul_I] at hs
  have him := congrArg Complex.im hs
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    mul_one, add_zero, zero_add, Complex.sinh_ofReal_re] at him
  dsimp [t] at him
  apply (eq_div_iff (by positivity : (4 * Real.pi^2 : ℝ) ≠ 0)).mpr
  calc
    _ = (2 * Real.pi * Real.sqrt q) *
        (K 0 ((-2 * Real.pi^2 * q : ℝ) : ℂ)).re := by field_simp; ring
    _ = _ := him

end WP.JT
