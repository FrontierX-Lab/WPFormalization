import WPFormalization.Volumes.FixedCuspProof

/-! Original fixed-cusp constant result, with the constant identified by the new prefactor. -/
noncomputable section
namespace WP

/- Corollary 1.2, constants may depend on fixed n. -/
/- Blueprint label(s): cor:constant
Paper v3: 1.2 [PDF 6]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "cor:constant"]
theorem zograf_constant (P : PsiTheory) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      |volumeModel P g n /
        ((2*g+n-3).factorial*(4*Real.pi^2)^(2*g+n-3)/Real.sqrt (Real.pi*g))-1| ≤ C/g := by
  exact zograf_constant_proof P n

end WP
