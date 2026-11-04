import Mathlib
/-! Strictly positive real coefficients from a scalar complex formal differential equation. -/
noncomputable section
namespace WP.Analysis
lemma complex_series_ode_coeff_pos (p g : PowerSeries ℂ) (c : ℝ) (hc : 0 < c)
    (hp : ∀ n, (PowerSeries.coeff n p).im = 0 ∧ 0 < (PowerSeries.coeff n p).re)
    (hg : PowerSeries.constantCoeff g = (c : ℂ))
    (he : PowerSeries.derivative g = p*g) :
    ∀ n, (PowerSeries.coeff n g).im = 0 ∧ 0 < (PowerSeries.coeff n g).re := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff,hg,Complex.ofReal_im,Complex.ofReal_re] using And.intro (rfl : (0 : ℝ)=0) hc
    | succ n =>
      have h := congrArg (PowerSeries.coeff n) he
      rw [PowerSeries.coeff_derivative,PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
      have him : (∑ i ∈ Finset.range (n+1), PowerSeries.coeff i p*PowerSeries.coeff (n-i) g).im = 0 := by
        change Complex.imCLM (∑ i ∈ Finset.range (n+1), PowerSeries.coeff i p*PowerSeries.coeff (n-i) g) = 0
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hig := (ih (n-i) (by omega)).1
        change (PowerSeries.coeff i p*PowerSeries.coeff (n-i) g).im = 0
        simp [Complex.mul_im,(hp i).1,hig]
      have hre : 0 < (∑ i ∈ Finset.range (n+1), PowerSeries.coeff i p*PowerSeries.coeff (n-i) g).re := by
        change 0 < Complex.reCLM (∑ i ∈ Finset.range (n+1), PowerSeries.coeff i p*PowerSeries.coeff (n-i) g)
        rw [map_sum]
        apply Finset.sum_pos
        · intro i hi
          have hig := ih (n-i) (by omega)
          change 0 < (PowerSeries.coeff i p*PowerSeries.coeff (n-i) g).re
          simp only [Complex.mul_re,(hp i).1,hig.1,zero_mul,sub_zero]
          exact mul_pos (hp i).2 hig.2
        · exact ⟨0,by simp⟩
      have hi := congrArg Complex.im h
      have hr := congrArg Complex.re h
      rw [him] at hi
      simp only [Complex.mul_im,Complex.mul_re,Complex.add_re,Complex.add_im,Complex.natCast_re,
        Complex.natCast_im,Complex.one_re,Complex.one_im,zero_add,mul_zero,sub_zero,add_zero] at hi hr
      have hn : (0 : ℝ) < n+1 := by positivity
      constructor
      · exact (mul_eq_zero.mp hi).resolve_right (ne_of_gt hn)
      · exact (mul_pos_iff_of_pos_right hn).mp (hr.symm ▸ hre)
end WP.Analysis
