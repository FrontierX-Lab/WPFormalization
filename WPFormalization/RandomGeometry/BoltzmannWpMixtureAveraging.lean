import WPFormalization.RandomGeometry.BoltzmannWpMixtureDefinitions
import WPFormalization.RandomGeometry.BoltzmannWpMixtureWeights
noncomputable section
universe u v
namespace WP.BoltzmannWp
open Set MeasureTheory Filter External
open scoped ENNReal Topology
variable {P:PsiTheory}
lemma countPMF_mu_weights_eventually (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P) :
    ∃ N:ℕ,∀ g≥N,∀ μ∈Ico (0:ℝ) muCritical,∀ n:ℕ,
      countPMF P g (parameter μ) n=ENNReal.ofReal (rawWeight G g μ n/partition G g μ) := by
  obtain ⟨N₁,hN₁⟩ := BoltzmannCusp.extendedLaw_original_weights_eventually P
  obtain ⟨N₂,hN₂⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨N₁+N₂+2,?_⟩
  intro g hg μ hμ n
  rw [countPMF,Measure.toPMF_apply,hN₁ g (by omega) _ (parameter_physical μ hμ) n,
    normalized_rawWeight_eq G g (by omega) μ hμ
      (hN₂ g (by omega) _ (parameter_physical μ hμ)).ne' n]

lemma wpMixture_mu_apply_eventually (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P) :
    ∃ N:ℕ,∀ g≥N,∀ μ∈Ico (0:ℝ) muCritical,∀ s:Set (Surface G g),MeasurableSet s →
      wpMixture G g (parameter μ) s=
        ∑'n,ENNReal.ofReal (rawWeight G g μ n/partition G g μ)*
          wpProbability G g n ((@Sigma.mk ℕ (fun m=>G.Moduli g m (fun _=>0)) n)⁻¹' s) := by
  obtain ⟨N,hN⟩ := countPMF_mu_weights_eventually P G
  refine ⟨N,?_⟩
  intro g hg μ hμ s hs
  rw [wpMixture_apply G g (parameter μ) s hs]
  simp_rw [hN g hg μ hμ]

lemma wpMixture_lintegral (G:WeilPeterssonGeometry.{u,v} P) (g:ℕ) (x:ℝ)
    (f:Surface G g→ℝ≥0∞) :
    ∫⁻X,f X ∂wpMixture G g x=∑'n,countPMF P g x n*∫⁻ω,f ⟨n,ω⟩ ∂wpProbability G g n := by
  rw [wpMixture,Probability.sigmaMixture,lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure,smul_eq_mul,
    (Probability.measurableEmbedding_sigmaMk n).lintegral_map]

lemma wpMixture_integral (G:WeilPeterssonGeometry.{u,v} P) (g:ℕ) (x:ℝ)
    (f:Surface G g→ℝ) (hi:Integrable f (wpMixture G g x)) :
    ∫X,f X ∂wpMixture G g x=∑'n,(countPMF P g x n).toReal*∫ω,f ⟨n,ω⟩ ∂wpProbability G g n :=
  Probability.integral_sigmaMixture _ _ f hi

lemma wpMixture_mu_integral_eventually (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P) :
    ∃ N:ℕ,∀ g≥N,∀ μ∈Ico (0:ℝ) muCritical,∀ f:Surface G g→ℝ,
      Integrable f (wpMixture G g (parameter μ)) →
      (∫X,f X ∂wpMixture G g (parameter μ))=
        ∑'n,(rawWeight G g μ n/partition G g μ)*∫ω,f ⟨n,ω⟩ ∂wpProbability G g n := by
  obtain ⟨N,hN⟩ := countPMF_mu_weights_eventually P G
  refine ⟨N,?_⟩
  intro g hg μ hμ f hi
  rw [wpMixture_integral G g (parameter μ) f hi]
  apply tsum_congr
  intro n
  rw [hN g hg μ hμ n,ENNReal.toReal_ofReal]
  exact div_nonneg (div_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hμ.1 n))
    (Nat.cast_nonneg _)) (tsum_nonneg fun m=>div_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hμ.1 m)) (Nat.cast_nonneg _))
end WP.BoltzmannWp
