import WPFormalization.Spectral.PantsConsequences

/-! Corollary 14.3 of the paper, with the original cusp and spectral-index
regimes. The actual geometric moments discharge the internal concentration
input; no paper-new concentration statement is a public hypothesis. -/
noncomputable section
universe u v w z
namespace WP.Spectral
open Filter MeasureTheory WP.External WP.RandomGeometry
open scoped Topology

@[blueprint "cor:many-spectrum"]
theorem many_small_eigenvalues (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (MI : MirzakhaniIntegration G H T) (S : SpectralGeometry H)
    (n j : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop)
    (hj : Tendsto j atTop atTop)
    (hsmall : Tendsto (fun g => (j g : ℝ) / pantsScale g (n g)) atTop (𝓝 0)) :
    Tendsto (fun g => (wpProbability G g (n g)).real
      {X | ∃ ℓ, S.positiveEigenvalue X (j g) = some ℓ ∧
        ℓ ≤ 12 * Real.sqrt ((j g : ℝ) / pantsScale g (n g))}) atTop (𝓝 1) := by
  exact many_eigenvalues_from_concentration P G H S n j hn hj hsmall
    (pants_concentration P G H T C MI n hn)

end WP.Spectral
