import WPFormalization.RandomGeometry.BoltzmannWpMixtureAveraging
import WPFormalization.Probability.SigmaMixtureConvergence
noncomputable section
universe u v w z
namespace WP.BoltzmannWp
open Set MeasureTheory Filter External
open scoped ENNReal Topology
variable {P:PsiTheory}

def observable (G:WeilPeterssonGeometry.{u,v} P) (g:ℕ) {E:Type w}
    (X:(n:ℕ)→G.Moduli g n (fun _=>0)→E) : Surface G g→E :=
  fun s=>X s.1 s.2

lemma wpMixture_aemeasurable (G:WeilPeterssonGeometry.{u,v} P) (g:ℕ) (x:ℝ)
    {E:Type w} [MeasurableSpace E] (X:Surface G g→E)
    (hX:∀n,AEMeasurable (fun ω:G.Moduli g n (fun _=>0)=>X ⟨n,ω⟩) (wpProbability G g n)) :
    AEMeasurable X (wpMixture G g x) :=
  Probability.aemeasurable_sigmaMixture _ _ X hX

lemma observable_aemeasurable (G:WeilPeterssonGeometry.{u,v} P) (g:ℕ) (x:ℝ)
    {E:Type w} [MeasurableSpace E] (X:(n:ℕ)→G.Moduli g n (fun _=>0)→E)
    (hX:∀n,AEMeasurable (X n) (wpProbability G g n)) :
    AEMeasurable (observable G g X) (wpMixture G g x) :=
  wpMixture_aemeasurable G g x _ hX

lemma wpMixture_bounded_integrable_eventually (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P) :
    ∃ N:ℕ,∀ g≥N,∀ x:ℝ,∀ f:Surface G g→ℝ,
      (∀n,AEMeasurable (fun ω:G.Moduli g n (fun _=>0)=>f ⟨n,ω⟩) (wpProbability G g n)) →
      ∀ B:ℝ,(∀X,‖f X‖≤B) → Integrable f (wpMixture G g x) := by
  obtain ⟨N,hN⟩ := wpProbability_probability_eventually P G
  refine ⟨N,?_⟩
  intro g hg x f hf B hB
  letI : ∀n,IsProbabilityMeasure (wpProbability G g n) := fun n=>hN g hg n
  exact Probability.integrable_sigmaMixture_ae_bounded _ _ f hf B hB

lemma wpMixture_mu_bounded_averaging_eventually (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P) :
    ∃ N:ℕ,∀ g≥N,∀ μ∈Ico (0:ℝ) muCritical,
      ∀ X:(n:ℕ)→G.Moduli g n (fun _=>0)→ℝ,
      (∀n,AEMeasurable (X n) (wpProbability G g n)) → ∀ B:ℝ,(∀n ω,‖X n ω‖≤B) →
      Integrable (observable G g X) (wpMixture G g (parameter μ)) ∧
      (∫s,observable G g X s ∂wpMixture G g (parameter μ))=
        ∑'n,(rawWeight G g μ n/partition G g μ)*∫ω,X n ω ∂wpProbability G g n := by
  obtain ⟨N₁,hN₁⟩ := wpMixture_bounded_integrable_eventually P G
  obtain ⟨N₂,hN₂⟩ := wpMixture_mu_integral_eventually P G
  refine ⟨N₁+N₂,?_⟩
  intro g hg μ hμ X hX B hB
  have hi:=hN₁ g (by omega) (parameter μ) (observable G g X) hX B (fun s=>hB s.1 s.2)
  exact ⟨hi,hN₂ g (by omega) μ hμ _ hi⟩

/-- Generic assembly lemma. The deterministic conditional-law producer remains
an explicit premise here; this lemma does not assert Theorem 14.4 or 14.5. -/
lemma lawConverges_wpMixture (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P)
    {E:Type w} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ωlimit:Type z} [MeasurableSpace Ωlimit]
    (X:(g n:ℕ)→G.Moduli g n (fun _=>0)→E) (Q:Measure Ωlimit) (Z:Ωlimit→E)
    (xs:ℕ→ℝ)
    (hX:∀ᶠg in atTop,∀n,AEMeasurable (X g n) (wpProbability G g n))
    (hseq:∀gs:ℕ→ℕ,Tendsto gs atTop atTop → ∀ns:ℕ→ℕ,
      Probability.LawConverges (fun j=>wpProbability G (gs j) (ns j))
        (fun j=>X (gs j) (ns j)) Q Z) :
    Probability.LawConverges (fun g=>wpMixture G g (xs g))
      (fun g=>observable G g (X g)) Q Z := by
  obtain ⟨N,hN⟩ := wpProbability_probability_eventually P G
  exact Probability.lawConverges_sigmaMixture _ X Q Z (fun g=>countPMF P g (xs g))
    (eventually_atTop.mpr ⟨N,hN⟩) hX hseq
end WP.BoltzmannWp
