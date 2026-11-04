import WPFormalization.Probability.PoissonClusterMeasures
noncomputable section
set_option maxHeartbeats 0
universe u
namespace WP.Probability.PoissonCluster
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
variable {J : Type u} [Countable J]

lemma indexedClusterMeasure_eq_compactParent_on_prefix
    (length : J→ℝ≥0→ℝ≥0) (hlength : ∀γ,Measurable (length γ))
    (ξ : Measure ℝ≥0) (L ε R : ℝ≥0) (hR : 2*L≤R)
    (hproper : ∀s : ℝ≥0,2*L<s→indexedKernelMeasure length s (Iic L)=0)
    (hsmall : ξ (Ioo (0:ℝ≥0) ε)=0)
    (B : Set ℝ≥0) (hB : MeasurableSet B) (hBL : B⊆Iic L) :
    indexedClusterMeasure length ξ B=
      indexedClusterMeasure length (ξ.restrict (Icc ε R)) B := by
  have havoid : ∀ᵐs ∂ξ,s∉Ioo (0:ℝ≥0) ε := by
    apply ae_iff.mpr
    change ξ ((Ioo (0:ℝ≥0) ε)ᶜ)ᶜ=0
    rwa [compl_compl]
  rw [indexedClusterMeasure,indexedClusterMeasure,Measure.sum_apply _ hB,
    Measure.sum_apply _ hB]
  apply tsum_congr
  intro γ
  rw [Measure.map_apply (hlength γ) hB,
    Measure.restrict_apply (hB.preimage (hlength γ)),
    Measure.map_apply (hlength γ) hB,
    Measure.restrict_apply (hB.preimage (hlength γ)),
    Measure.restrict_apply ((hB.preimage (hlength γ)).inter measurableSet_Ioi)]
  apply measure_congr
  filter_upwards [havoid] with s hs
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_Ioi,Set.mem_Icc]
  apply propext
  constructor
  · intro h
    refine ⟨h,?_,?_⟩
    · exact le_of_not_gt (fun hlt => hs ⟨h.2,hlt⟩)
    · by_contra hn
      have hz := hproper s (hR.trans_lt (lt_of_not_ge hn))
      exact ((indexedKernelMeasure_eq_zero_iff length s _ measurableSet_Iic).mp hz γ) (hBL h.1)
  · exact fun h => h.1

lemma indexedClusterMeasure_restrict_prefix_eq_compactParent
    (length : J→ℝ≥0→ℝ≥0) (hlength : ∀γ,Measurable (length γ))
    (ξ : Measure ℝ≥0) (L ε R : ℝ≥0) (hR : 2*L≤R)
    (hproper : ∀s : ℝ≥0,2*L<s→indexedKernelMeasure length s (Iic L)=0)
    (hsmall : ξ (Ioo (0:ℝ≥0) ε)=0) :
    (indexedClusterMeasure length ξ).restrict (Iic L)=
      (indexedClusterMeasure length (ξ.restrict (Icc ε R))).restrict (Iic L) := by
  ext B hB
  rw [Measure.restrict_apply hB,Measure.restrict_apply hB]
  exact indexedClusterMeasure_eq_compactParent_on_prefix length hlength ξ L ε R hR hproper hsmall
    (B∩Iic L) (hB.inter measurableSet_Iic) inter_subset_right

end WP.Probability.PoissonCluster
