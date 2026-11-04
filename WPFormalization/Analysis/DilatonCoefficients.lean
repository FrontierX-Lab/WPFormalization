import WPFormalization.Analysis.KernelJets

/-! Exact normalized H-kernel coefficients for the shifted dilaton equation. -/
noncomputable section
namespace WP

lemma coeff_barH_interior (Y : ℝ) (hy : Y ≠ y₀) (n : ℕ) :
    coeff (barH Y) n = (r Y:ℂ)^n *
      (3*iteratedDeriv (n+1) X Y)/((oddFactorial (n+1):ℂ)*(a Y:ℂ)) := by
  have he : barH Y = fun z : ℂ => H Y ((r Y:ℂ)*z)/(a Y:ℂ) := by
    funext z
    simp [barH,hy]
  unfold coeff
  rw [he,iteratedDeriv_div_const,Analysis.iteratedDeriv_comp_mul_left,mul_zero,
    iteratedDeriv_H_zero]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

lemma coeff_barH_interior_real (Y : ℝ) (hy : Y ≠ y₀) (n : ℕ) :
    coeff (barH Y) n =
      ((r Y^n*(3*(iteratedDeriv (n+1) X Y).re)/
        ((oddFactorial (n+1):ℝ)*a Y):ℝ):ℂ) := by
  have hx : iteratedDeriv (n+1) X (Y:ℂ) = ((iteratedDeriv (n+1) X (Y:ℂ)).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using iteratedDeriv_X_im_ofReal (n+1) Y
  rw [coeff_barH_interior Y hy,hx]
  simp only [Complex.ofReal_re]
  push_cast
  ring

lemma realCoeff_barH_interior (Y : ℝ) (hy : Y ≠ y₀) (n : ℕ) :
    realCoeff (barH Y) n = r Y^n*(3*(iteratedDeriv (n+1) X Y).re)/
      ((oddFactorial (n+1):ℝ)*a Y) := by
  unfold realCoeff
  rw [coeff_barH_interior_real Y hy,Complex.ofReal_re]

end WP
