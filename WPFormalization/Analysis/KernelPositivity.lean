import WPFormalization.Analysis.KKernelPositivity

/-! The full kernel-positivity theorem is proved from the defining kernels.
The sole deferred input is the classical real-zero theorem for J0 used to
identify the zero-free parameter disk. No new K/H-kernel result is assumed. -/
noncomputable section
namespace WP

/- Lemma 2.2. Taylor series in the parameter are asserted to converge, as well as positivity. -/
/- Blueprint label(s): lem:kernel-positivity
Paper v3: 2.2 [PDF 17]
Status: CONDITIONAL (classical J0 zero distribution only)
-/
@[blueprint "lem:kernel-positivity"]
theorem kernel_positivity :
    (∀ m : ℕ, 0 < m →
      (∀ Y : ℂ, ‖Y‖ < y₀ → AnalyticAt ℂ (logKernelCoeff m) Y) ∧
      (∀ q, 0 ≤ (iteratedDeriv q (logKernelCoeff m) 0).re) ∧
      0 < (logKernelCoeff m 0).re ∧
      (∀ Y : ℂ, ‖Y‖ < y₀ →
        HasSum (fun q => coeff (logKernelCoeff m) q * Y^q) (logKernelCoeff m Y))) ∧
    (∀ Y ∈ Set.Ico 0 y₀, ∀ h : ℝ, 0 < h → ∀ m,
      0 < realCoeff (fun z => Complex.exp (-(h : ℂ) * Complex.log (H Y z))) m) ∧
    (∀ Y ∈ Set.Ico 0 y₀, ∀ m, 0 ≤ realCoeff (fun z => -deriv (H Y) z / H Y z) m) ∧
    (∀ l q : ℕ,
      0 ≤ realCoeff (fun Y => deriv X Y * coeff (fun z => (K Y z)⁻¹) l) q ∧
      0 ≤ realCoeff (fun Y => coeff (fun z => (K Y z)⁻¹) l) q) ∧
    (∀ q, 0 ≤ realCoeff (fun Y => (deriv X Y)⁻¹) q) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro m hm
    refine ⟨?_,?_,?_,?_⟩
    · intro Y hY
      exact Analysis.logKernelCoeff_analyticAt m Y (derivX_ne_zero_of_norm_lt Y hY)
    · exact Analysis.logKernelCoeff_derivative_nonneg m hm
    · exact Analysis.logKernelCoeff_zero_pos m hm
    · exact Analysis.logKernelCoeff_hasSum m
  · exact fun Y hY h hh m => Analysis.H_negative_power_coeff_pos Y hY h hh m
  · exact fun Y hY m => (Analysis.H_logarithmic_coeff_pos Y hY m).le
  · intro l q
    exact ⟨Analysis.normalized_K_inverse_parameter_nonneg l q,Analysis.reciprocal_K_parameter_nonneg l q⟩
  · exact fun q => (a_inverse_coeff_pos q).le


end WP
