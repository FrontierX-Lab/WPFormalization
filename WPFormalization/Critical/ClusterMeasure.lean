import WPFormalization.Probability.PoissonClusterMeasures
import WPFormalization.Critical.ClusterLaplace
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology CompactlySupported Classical
variable (F : Family.{u,v})

instance primitive_countable : Countable F.Primitive := by
  have hsub : (Set.univ : Set F.Primitive)⊆⋃m : ℕ,(F.short referenceWaist (m:ℝ) : Set F.Primitive) := by
    intro γ _
    obtain ⟨m,hm⟩:=exists_nat_ge (F.length referenceWaist γ)
    exact Set.mem_iUnion.mpr ⟨m,(F.mem_short referenceWaist _ _).mpr hm⟩
  exact Set.countable_univ_iff.mp ((Set.countable_iUnion
    (fun m : ℕ=>(F.short referenceWaist (m:ℝ)).finite_toSet.countable)).mono hsub)

/- The zero extension is only an implementation of the positive-parent map;
all parent mass at zero is removed by indexedClusterMeasure itself. -/
def markedLengthNN (γ : F.Primitive) (s : ℝ≥0) : ℝ≥0 :=
  if hs : 0<s then Real.toNNReal (F.length ⟨(s:ℝ),by exact_mod_cast hs⟩ γ) else 0

lemma markedLengthNN_pos (γ : F.Primitive) (s : ℝ≥0) (hs : 0<s) :
    markedLengthNN F γ s=Real.toNNReal (F.length ⟨(s:ℝ),by exact_mod_cast hs⟩ γ) := by
  simp only [markedLengthNN,dif_pos hs]

lemma markedLengthNN_measurable (D : DeformationClassics F) (γ : F.Primitive) :
    Measurable (markedLengthNN F γ) := by
  let e : Ioi (0:ℝ≥0)→Waist:=fun s=>⟨(s.val:ℝ),by exact_mod_cast s.property⟩
  have he : Continuous e := Continuous.subtype_mk (NNReal.continuous_coe.comp continuous_subtype_val) _
  exact Measurable.dite
    (continuous_real_toNNReal.comp ((marked_length_continuous F D γ).comp he)).measurable
    measurable_const measurableSet_Ioi

lemma indexedKernelMeasure_markedLengthNN_pos (s : ℝ≥0) (hs : 0<s) :
    PoissonCluster.indexedKernelMeasure (markedLengthNN F) s=
      measure F ⟨(s:ℝ),by exact_mod_cast hs⟩ := by
  simp only [PoissonCluster.indexedKernelMeasure,measure,markedLengthNN,dif_pos hs]

lemma markedLengthNN_waistClass (s : ℝ≥0) : markedLengthNN F F.waistClass s=s := by
  by_cases hs : 0<s
  · rw [markedLengthNN_pos F _ s hs,F.length_waist,Real.toNNReal_coe]
  · have hz : s=0 := le_antisymm (le_of_not_gt hs) (by positivity)
    simp [markedLengthNN,hs,hz]

def clusterMeasure (ξ : Measure ℝ≥0) : Measure ℝ≥0 :=
  PoissonCluster.indexedClusterMeasure (markedLengthNN F) ξ

lemma cluster_kernel_uniform_bound (L : ℝ≥0) :
    ∃C : ℝ≥0∞,C<∞ ∧ ∀s : ℝ≥0,0<s→
      PoissonCluster.indexedKernelMeasure (markedLengthNN F) s (Iic L)≤C := by
  obtain ⟨C,hC,hbound⟩:=cluster_prefix_uniform_bound F L
  refine ⟨ENNReal.ofReal C,ENNReal.ofReal_lt_top,fun s hs=>?_⟩
  rw [indexedKernelMeasure_markedLengthNN_pos F s hs]
  apply (ENNReal.le_ofReal_iff_toReal_le ?_ hC.le).mpr
  · exact hbound _
  · rw [measure_Iic]
    exact ENNReal.natCast_ne_top _

lemma cluster_kernel_proper
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0) :
    ∀(L s : ℝ≥0),2*L<s→PoissonCluster.indexedKernelMeasure (markedLengthNN F) s (Iic L)=0 := by
  intro L s hlarge
  have hs : 0<s := lt_of_le_of_lt (by positivity : 0≤2*L) hlarge
  rw [indexedKernelMeasure_markedLengthNN_pos F s hs]
  exact hproper _ L (by exact_mod_cast hlarge)

def clusterPointMeasure (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (ξ : PointMeasure ℝ≥0) : PointMeasure ℝ≥0 :=
  PoissonCluster.indexedClusterPointMeasure (markedLengthNN F) (markedLengthNN_measurable F D) ξ
    (cluster_kernel_uniform_bound F) (cluster_kernel_proper F hproper)

lemma clusterPointMeasure_toMeasure (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (ξ : PointMeasure ℝ≥0) :
    (clusterPointMeasure F D hproper ξ).toMeasure=clusterMeasure F ξ.toMeasure := rfl

lemma clusterMeasure_lintegral_ofReal (D : DeformationClassics F) (ξ : Measure ℝ≥0)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀x,0≤f x) :
    (∫⁻x,ENNReal.ofReal (f x) ∂clusterMeasure F ξ)=
      ∫⁻s,ENNReal.ofReal (testPairingNN F f s) ∂ξ := by
  rw [clusterMeasure,PoissonCluster.indexedClusterMeasure_lintegral _
    (markedLengthNN_measurable F D) ξ (fun x=>ENNReal.ofReal (f x))
    (by fun_prop)]
  rw [←lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0<s
  · rw [Set.indicator_of_mem (show s∈Ioi (0:ℝ≥0) from hs)]
    rw [indexedKernelMeasure_markedLengthNN_pos F s hs,testPairingNN_pos F f s hs]
    exact (ofReal_integral_eq_lintegral_ofReal f.integrable (Eventually.of_forall hf)).symm
  · simp [Set.indicator,Set.mem_Ioi,hs,testPairingNN]

lemma clusterMeasure_integral_nonneg (D : DeformationClassics F) (ξ : Measure ℝ≥0)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀x,0≤f x) :
    (∫x,f x ∂clusterMeasure F ξ)=∫s,testPairingNN F f s ∂ξ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) f.continuous.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (testPairingNN_nonneg F f hf))
      (testPairingNN_measurable F D f).aestronglyMeasurable,
    clusterMeasure_lintegral_ofReal F D ξ f hf]

end WP.Critical.PantsCluster
