import WPFormalization.HigherOrder.AbsoluteVolumeProof
noncomputable section
namespace WP
open Filter
open scoped Topology
/- Theorem 11.1, uniform error and sharp lower limit. -/
/- Blueprint label(s): thm:absolute
Paper v3: 11.1 [PDF 48]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "thm:absolute"]
theorem absolute_volume (P : PsiTheory) :
    (∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ n : ℕ,
      |volumeModel P g n/leadingVolume g n-1| ≤ C/g) ∧
    (7/12-17/(6*Real.pi^2) ≤ Filter.liminf
      (fun g : ℕ => (g : ℝ)*⨆ n : ℕ, |volumeModel P g n/leadingVolume g n-1|) atTop) ∧
    0 < 7/12-17/(6*Real.pi^2) := by
  exact HigherOrder.absolute_volume_proof P

end WP
