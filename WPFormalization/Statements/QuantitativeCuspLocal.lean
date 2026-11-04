import WPFormalization.Volumes.QuantitativeCuspLocalProof
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Proposition D.1; sup over integer k is stated pointwise with a common bound. -/
/- Blueprint label(s): prop:quantitative-local
Paper v3: D.1 [PDF 88]
Status: CONDITIONALLY_PROVED; PsiTheory and registered classical inputs remain
-/
@[blueprint "prop:quantitative-local"]
theorem quantitative_cusp_local (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C κ M₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < M₀ ∧
    ∀ g : ℕ, ∀ x ∈ Set.Ioo 0 xCritical,
      let h : ℝ := complexity g p
      let μ := h*Psi x
      let σ := Real.sqrt (h*euler Psi x)
      M₀ ≤ min h μ → ∀ k : ℤ,
        |σ*(if 0 ≤ k then cuspMass P g p k.toNat x else 0) -
          Real.exp (-((k : ℝ)-μ)^2/(2*σ^2))/Real.sqrt (2*Real.pi)| ≤
          C*Real.rpow (min h μ) (-κ) := by
  exact quantitative_cusp_local_proof P p hp

end WP
