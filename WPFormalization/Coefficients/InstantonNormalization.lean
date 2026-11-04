import WPFormalization.Coefficients.OneBoundaryBracketModel

/-! Exact algebraic normalization in §13.7. The coefficient is the genuine
Taylor coefficient of the inverse power of H(0), and the model is the
previously defined one-boundary bracket model. No contour prediction or
geometric asymptotic is assumed in these identities. -/

set_option autoImplicit false
noncomputable section
namespace WP.Coefficients

/-- The coefficient model in the original, unscaled H(0) coordinate. -/
theorem oneBoundaryBracketModel_eq_unscaled (g k : ℕ) (hk : k ≤ 3*g-2) :
    oneBoundaryBracketModel g k =
      (4 : ℝ)^k * 3^(complexity g 1) * Real.Gamma (complexity g 1) / 4^g *
        (2*Real.pi^2)^(3*g-2-k) * unscaledCoeff (complexity g 1) (3*g-2-k) := by
  have hdef : deficit g [k] = 3*g-2-k := by
    simp only [deficit, List.length_singleton, List.sum_singleton, dimension]
    omega
  have hN : 3*g-2 = k+(3*g-2-k) := by omega
  have hscale : (4 : ℝ)^(3*g-2) * (Real.pi^2/2)^(3*g-2-k) =
      4^k * (2*Real.pi^2)^(3*g-2-k) := by
    calc
      _ = 4^k * (4*(Real.pi^2/2))^(3*g-2-k) := by
        rw [show (4 : ℝ)^(3*g-2) = 4^k*4^(3*g-2-k) by rw [hN, pow_add]; simp]
        rw [mul_pow]
        ring
      _ = _ := by congr 2; ring
  simp only [oneBoundaryBracketModel, model, List.length_singleton, hdef,
    harmonicCoeff_zero_unscaled, r_zero_parameter]
  calc
    _ = ((4 : ℝ)^(3*g-2) * (Real.pi^2/2)^(3*g-2-k)) *
        (3^(complexity g 1) * Real.Gamma (complexity g 1) / 4^g) *
        unscaledCoeff (complexity g 1) (3*g-2-k) := by ring
    _ = _ := by rw [hscale]; ring

/-- The exact degree-independent factor two in the instanton residue dictionary,
written using natural powers in the denominator. -/
theorem instanton_coefficient_normalization_div (g k : ℕ) (hg : 1 ≤ g)
    (hk : k ≤ 3*g-2) :
    Real.Gamma (complexity g 1) * (3/2 : ℝ)^(complexity g 1) *
        (2*Real.pi^2)^(3*g-2-k) * unscaledCoeff (complexity g 1) (3*g-2-k) =
      2 / (4 : ℝ)^k * oneBoundaryBracketModel g k := by
  have hh : complexity g 1+1 = 2*g := by unfold complexity; omega
  have h4 : (4 : ℝ)^g = 2 * 2^(complexity g 1) := by
    calc
      _ = (2 : ℝ)^(2*g) := by rw [pow_mul]; norm_num
      _ = 2 * 2^(complexity g 1) := by rw [← hh, pow_succ]; ring
  rw [oneBoundaryBracketModel_eq_unscaled g k hk, div_pow, h4]
  field_simp

/-- The exact normalization as printed in §13.7, including the integer
negative power `4^(-k)`. -/
theorem instanton_coefficient_normalization (g k : ℕ) (hg : 1 ≤ g)
    (hk : k ≤ 3*g-2) :
    Real.Gamma (complexity g 1) * (3/2 : ℝ)^(complexity g 1) *
        (2*Real.pi^2)^(3*g-2-k) * unscaledCoeff (complexity g 1) (3*g-2-k) =
      2 * (4 : ℝ)^(-(k : ℤ)) * oneBoundaryBracketModel g k := by
  simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using
    instanton_coefficient_normalization_div g k hg hk

end WP.Coefficients
