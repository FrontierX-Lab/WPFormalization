import WPFormalization.Volumes.BoundarySaddleComparison
import WPFormalization.Volumes.BoundaryFinalAssembly
/-! Proposition 9.4 for every cusp count, uniformly over the original fixed
number of bounded nonzero geodesic lengths. The unbounded cusp branch uses
the actual boundary generating function and its Gaussian local limit; the
bounded cusp branch and exact finite reindexing cover the remaining cases. -/
noncomputable section
namespace WP
open Set Filter
open scoped Topology

lemma bounded_boundaries_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (L₀ : ℝ) (hL : 0 ≤ L₀) :
    ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ n : ℕ, p ≤ n →
      ∀ L : Fin n → ℝ, (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L₀) →
      (∀ i, p ≤ i.val → L i = 0) →
        |boundaryVolumeModel P g n L /
          (volumeModel P g n * ∏ i : Fin n,
            boundaryFactor (densityY ((n : ℝ)/g)) (L i))-1| ≤ ε := by
  apply BoundaryConvolution.bounded_boundaries_of_prefix_uniform P p L₀
  apply BoundaryConvolution.boundary_prefix_uniform_of_sequential P p hp L₀ hL
  exact BoundaryConvolution.boundary_prefix_sequential P p hp L₀ hL

end WP
