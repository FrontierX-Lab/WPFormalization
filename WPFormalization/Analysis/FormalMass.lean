import WPFormalization.Statements.Basic

/-! Finite coefficient identity behind Eq.4.12. The normalized-kernel relation
is used algebraically, before division by the positive harmonic coefficient.
-/
noncomputable section
namespace WP.Analysis
open PowerSeries

lemma formalMass_coeff_euler (p : PowerSeries ℝ) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.X*PowerSeries.derivative p) =
      (m : ℝ)*PowerSeries.coeff m p := by
  cases m with
  | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      simp
  | succ m =>
      rw [coeff_succ_X_mul, coeff_derivative]
      push_cast
      ring

/-- Formal identity in the numerator of the harmonic mass equation. -/
theorem formal_mass_identity (f k : PowerSeries ℝ)
    (hf : constantCoeff f ≠ 0) (hk : constantCoeff k ≠ 0)
    (hrel : k = f+C (2/3 : ℝ)*PowerSeries.X*PowerSeries.derivative f)
    (h : ℕ) (hh : 2 ≤ h) :
    k⁻¹*(f⁻¹^(h-1)-C (2/(3*((h : ℝ)-1)))*PowerSeries.X*
      PowerSeries.derivative (f⁻¹^(h-1))) = f⁻¹^h := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hh
  have hfpower : f*f⁻¹^(2+n) = f⁻¹^(1+n) := by
    rw [show 2+n = (1+n)+1 by omega, pow_succ]
    calc
      _ = f⁻¹^(1+n)*(f*f⁻¹) := by ring
      _ = f⁻¹^(1+n) := by rw [PowerSeries.mul_inv_cancel f hf]; ring
  have hcast : ((2+n : ℕ) : ℝ)-1 = (1+n : ℕ) := by push_cast; ring
  have hscalar : C (2/(3*((1+n : ℕ) : ℝ))) * ((1+n : ℕ) : PowerSeries ℝ) =
      C (2/3 : ℝ) := by
    change C (2/(3*((1+n : ℕ) : ℝ)))*C ((1+n : ℕ) : ℝ) = _
    rw [← map_mul]
    congr 1
    have hn : ((1+n : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hd : PowerSeries.derivative (f⁻¹^(1+n)) =
      -((1+n : ℕ) : PowerSeries ℝ)*f⁻¹^(2+n)*PowerSeries.derivative f := by
    rw [PowerSeries.derivative_pow, PowerSeries.derivative_inv']
    rw [show 1+n-1 = n by omega, show 2+n = n+2 by omega, pow_add]
    ring
  have hinside : f⁻¹^(1+n)-C (2/(3*((1+n : ℕ) : ℝ)))*PowerSeries.X*
      PowerSeries.derivative (f⁻¹^(1+n)) = k*f⁻¹^(2+n) := by
    rw [hd, hrel]
    have hs := congrArg (fun a : PowerSeries ℝ =>
      a*PowerSeries.X*f⁻¹^(2+n)*PowerSeries.derivative f) hscalar
    calc
      _ = f⁻¹^(1+n)+(C (2/(3*((1+n : ℕ) : ℝ)))*((1+n : ℕ) : PowerSeries ℝ))*
          PowerSeries.X*f⁻¹^(2+n)*PowerSeries.derivative f := by ring
      _ = f⁻¹^(1+n)+C (2/3 : ℝ)*PowerSeries.X*f⁻¹^(2+n)*PowerSeries.derivative f := by rw [hscalar]
      _ = _ := by rw [add_mul, hfpower]; ring
  rw [show 2+n-1 = 1+n by omega, hcast, hinside, ← mul_assoc,
    PowerSeries.inv_mul_cancel k hk, one_mul]

/-- The finite convolution, with no denominator or nonzero coefficient assumption. -/
theorem formal_mass_coefficients (f k : PowerSeries ℝ)
    (hf : constantCoeff f ≠ 0) (hk : constantCoeff k ≠ 0)
    (hrel : k = f+C (2/3 : ℝ)*PowerSeries.X*PowerSeries.derivative f)
    (h m : ℕ) (hh : 2 ≤ h) :
    (∑ l ∈ Finset.range (m+1), PowerSeries.coeff l k⁻¹*
      PowerSeries.coeff (m-l) (f⁻¹^(h-1)) *
      (1-2*((m-l : ℕ) : ℝ)/(3*((h : ℝ)-1)))) =
        PowerSeries.coeff m (f⁻¹^h) := by
  have he := congrArg (PowerSeries.coeff m) (formal_mass_identity f k hf hk hrel h hh)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  simp only [mul_assoc, map_sub, PowerSeries.coeff_C_mul, formalMass_coeff_euler] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro l hl
  ring

end WP.Analysis
