import WPFormalization.External.Bessel

/-! Explicit Bessel-series dictionary and the zero-free parameter disk.
The derivative/series bridge is proved from the actual origin jets. Only the
classical J0 zero distribution is deferred in External/Bessel.
-/
noncomputable section
namespace WP
open Filter
open scoped Topology

lemma complex_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2 = z := by
  simpa [Complex.sqrt] using Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

lemma derivX_eq_besselJ0 (z : ℂ) : deriv X z = besselJ₀ (2*Complex.sqrt z) := by
  have hf : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  rw [← Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) hf,besselJ₀]
  apply tsum_congr
  intro n
  rw [← iteratedDeriv_succ',iteratedDeriv_X_succ_zero]
  simp only [sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
  have hs : (Complex.sqrt z)^(2*n) = z^n := by rw [pow_mul,complex_sqrt_sq]
  rw [hs]
  ring

/-- A classical J0 zero pulls back to a positive real zero in the X coordinate. -/
lemma derivX_zero_real_pos (z : ℂ) (hz : deriv X z = 0) : z.im = 0 ∧ 0 < z.re := by
  have hj : besselJ₀ (2*Complex.sqrt z) = 0 := by rw [← derivX_eq_besselJ0 z]; exact hz
  have hi := External.besselJ0_zeros_real (2*Complex.sqrt z) hj
  have hsi : (Complex.sqrt z).im = 0 := by simpa using hi
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    have h0 : deriv X (0 : ℂ) = 1 := by
      simpa [iteratedDeriv_one] using iteratedDeriv_X_succ_zero 0
    simpa [h0] using hz
  have hs0 : (Complex.sqrt z).re ≠ 0 := by
    intro h
    have he : Complex.sqrt z = 0 := by apply Complex.ext <;> simp [h,hsi]
    apply hz0
    rw [← complex_sqrt_sq z,he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have he : z.re = (Complex.sqrt z).re^2 := by
    have ht := congrArg Complex.re (complex_sqrt_sq z)
    simpa [pow_two,Complex.mul_re,hsi] using ht.symm
  constructor
  · have ht := congrArg Complex.im (complex_sqrt_sq z)
    simpa [pow_two,Complex.mul_im,hsi] using ht.symm
  · rw [he]
    exact sq_pos_of_ne_zero hs0

lemma derivX_ne_zero_of_norm_lt (z : ℂ) (hz : ‖z‖ < y₀) : deriv X z ≠ 0 := by
  intro he
  obtain ⟨hi,hp⟩ := derivX_zero_real_pos z he
  have hc : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have hr : y₀ ≤ z.re := by
    apply csInf_le
    · exact ⟨0,fun x hx => hx.1.le⟩
    · exact ⟨hp,by rw [← hc]; exact he⟩
  have hn : ‖z‖ = z.re := by
    calc
      ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hc
      _ = z.re := by simp [abs_of_pos hp]
  rw [hn] at hz
  exact (not_lt_of_ge hr) hz

end WP
