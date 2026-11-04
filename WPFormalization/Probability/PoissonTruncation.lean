import WPFormalization.Probability.LawConvergenceTruncation
import WPFormalization.Probability.PoissonCountContinuity

noncomputable section
namespace WP.Probability
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Uniformly negligible tails and convergence of finite Poisson approximants
imply the actual count-vector law. The bad events may depend on the cutoff. -/
theorem lawConverges_poisson_of_truncations {d:ℕ} {Ω:ℕ→Type*}
    [∀j,MeasurableSpace (Ω j)] (μ:(j:ℕ)→Measure (Ω j))
    (X:(j:ℕ)→Ω j→Fin d→ℕ) (Y:(K j:ℕ)→Ω j→Fin d→ℕ)
    (rK:ℕ→Fin d→ℝ≥0) (r:Fin d→ℝ≥0)
    (hprob:∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX:∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hY:∀K,∀ᶠj in atTop,AEMeasurable (Y K j) (μ j))
    (A:(K j:ℕ)→Set (Ω j)) (hA:∀K,∀ᶠj in atTop,MeasurableSet (A K j))
    (hXY:∀K,∀ᶠj in atTop,∀ω,ω∉A K j→X j ω=Y K j ω)
    (htail:∀ε:ℝ,0<ε→∃K0:ℕ,∀K:ℕ,K0≤K→∀ᶠj in atTop,(μ j).real (A K j)≤ε)
    (hLaw:∀K,LawConverges μ (Y K) (productPoissonMeasure (rK K)) id)
    (hr:∀i,Tendsto (fun K=>rK K i) atTop (𝓝 (r i))) :
    LawConverges μ X (productPoissonMeasure r) id := by
  exact lawConverges_of_truncations μ X Y (fun K=>productPoissonMeasure (rK K))
    (fun _ z=>z) (productPoissonMeasure r) id hprob hX hY A hA hXY htail hLaw
    (product_poisson_law_tendsto rK r hr)

end WP.Probability
