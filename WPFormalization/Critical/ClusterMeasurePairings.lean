import WPFormalization.Critical.ClusterMeasure
import WPFormalization.Probability.PoissonClusterCompactParents
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology CompactlySupported Classical
variable (F : Family.{u,v})

/- The waist belongs to the full primitive reference catalog exactly once.
The remainder has precisely the complementary primitive indices. -/
def clusterRemainderMeasure (ξ : Measure ℝ≥0) : Measure ℝ≥0 :=
  Measure.sum (fun γ : ↥({F.waistClass} : Set F.Primitive)ᶜ =>
    (ξ.restrict (Ioi (0:ℝ≥0))).map (markedLengthNN F γ.val))

lemma clusterMeasure_eq_parent_add_remainder (ξ : Measure ℝ≥0) :
    clusterMeasure F ξ = ξ.restrict (Ioi (0:ℝ≥0)) + clusterRemainderMeasure F ξ := by
  let μ : F.Primitive → Measure ℝ≥0 := fun γ =>
    (ξ.restrict (Ioi (0:ℝ≥0))).map (markedLengthNN F γ)
  have hs : Measure.sum (fun γ : ({F.waistClass} : Set F.Primitive) => μ γ.val) =
      ξ.restrict (Ioi (0:ℝ≥0)) := by
    letI : Unique ↥({F.waistClass} : Set F.Primitive) :=
      { default := ⟨F.waistClass,by simp⟩
        uniq := fun γ => Subtype.ext (Set.mem_singleton_iff.mp γ.property) }
    have hwaist : markedLengthNN F F.waistClass = fun s => s :=
      funext (markedLengthNN_waistClass F)
    ext B hB
    rw [Measure.sum_apply _ hB,tsum_fintype]
    simp [μ,hwaist]
  have hh := Measure.sum_add_sum_compl ({F.waistClass} : Set F.Primitive) μ
  rw [hs] at hh
  exact hh.symm

lemma testPairingNN_sub (f g : C_c(ℝ≥0,ℝ)) (s : ℝ≥0) :
    testPairingNN F (f-g) s = testPairingNN F f s - testPairingNN F g s := by
  by_cases hs : 0<s
  · simp only [testPairingNN_pos F _ s hs,
      CompactlySupportedContinuousMap.coe_sub,Pi.sub_apply]
    exact integral_sub f.integrable g.integrable
  · simp [testPairingNN,hs]

lemma testPairingNN_integrable_signed_of_prefix_cutoff (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (f : C_c(ℝ≥0,ℝ)) (ξ : Measure ℝ≥0) [IsLocallyFiniteMeasure ξ] :
    Integrable (testPairingNN F f) ξ := by
  obtain ⟨K,hK,hsK⟩ := testPairingNN_compact_support_of_prefix_cutoff F hproper f
  obtain ⟨C,_,hC⟩ := testPairingNN_uniform_bound F f
  apply (integrableOn_iff_integrable_of_support_subset hsK).mp
  exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (testPairingNN_measurable F D f).aestronglyMeasurable (Eventually.of_forall hC)

/- Signed identification requires genuine integrability. In particular no
Bochner convention at a divergent nonnegative integral is used by consumers. -/
lemma clusterMeasure_integral_of_integrable_pairings (D : DeformationClassics F)
    (ξ : Measure ℝ≥0) [IsLocallyFiniteMeasure (clusterMeasure F ξ)]
    (hpair : ∀f : C_c(ℝ≥0,ℝ),Integrable (testPairingNN F f) ξ)
    (f : C_c(ℝ≥0,ℝ)) :
    (∫x,f x ∂clusterMeasure F ξ) = ∫s,testPairingNN F f s ∂ξ := by
  let fp : C_c(ℝ≥0,ℝ) := f ⊔ 0
  let fm : C_c(ℝ≥0,ℝ) := (-f) ⊔ 0
  have hp : ∀x,0≤fp x := fun x => le_max_right _ _
  have hm : ∀x,0≤fm x := fun x => le_max_right _ _
  have hsplit : f=fp-fm := by
    ext x
    simp only [fp,fm,CompactlySupportedContinuousMap.sub_apply,
      CompactlySupportedContinuousMap.sup_apply,CompactlySupportedContinuousMap.neg_apply,
      CompactlySupportedContinuousMap.zero_apply]
    exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hsplit]
  simp only [CompactlySupportedContinuousMap.coe_sub,Pi.sub_apply,testPairingNN_sub]
  rw [integral_sub fp.integrable fm.integrable,integral_sub (hpair fp) (hpair fm),
    clusterMeasure_integral_nonneg F D ξ fp hp,clusterMeasure_integral_nonneg F D ξ fm hm]

lemma clusterPointMeasure_integral (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (ξ : PointMeasure ℝ≥0) (f : C_c(ℝ≥0,ℝ)) :
    (∫x,f x ∂(clusterPointMeasure F D hproper ξ).toMeasure)=
      ∫s,testPairingNN F f s ∂ξ.toMeasure := by
  change (∫x,f x ∂clusterMeasure F ξ.toMeasure)=_
  letI : IsLocallyFiniteMeasure (clusterMeasure F ξ.toMeasure) := by
    rw [←clusterPointMeasure_toMeasure F D hproper ξ]
    infer_instance
  exact clusterMeasure_integral_of_integrable_pairings F D ξ.toMeasure
    (fun f => testPairingNN_integrable_signed_of_prefix_cutoff F D hproper f ξ.toMeasure) f

def compactWaistClusterPointMeasure (D : DeformationClassics F) (ξ : PointMeasure ℝ≥0)
    (W : RelCompactBorelWindow ℝ≥0) : PointMeasure ℝ≥0 :=
  PoissonCluster.compactParentClusterPointMeasure (markedLengthNN F)
    (markedLengthNN_measurable F D) ξ W (cluster_kernel_uniform_bound F)

lemma compactWaistClusterPointMeasure_toMeasure (D : DeformationClassics F)
    (ξ : PointMeasure ℝ≥0) (W : RelCompactBorelWindow ℝ≥0) :
    (compactWaistClusterPointMeasure F D ξ W).toMeasure=
      clusterMeasure F (ξ.toMeasure.restrict W.carrier) := rfl

lemma compactWaistClusterPointMeasure_integral (D : DeformationClassics F)
    (ξ : PointMeasure ℝ≥0) (W : RelCompactBorelWindow ℝ≥0) (f : C_c(ℝ≥0,ℝ)) :
    (∫x,f x ∂(compactWaistClusterPointMeasure F D ξ W).toMeasure)=
      ∫s in W.carrier,testPairingNN F f s ∂ξ.toMeasure := by
  change (∫x,f x ∂clusterMeasure F (ξ.toMeasure.restrict W.carrier))=_
  letI : IsLocallyFiniteMeasure (clusterMeasure F (ξ.toMeasure.restrict W.carrier)) := by
    rw [←compactWaistClusterPointMeasure_toMeasure F D ξ W]
    infer_instance
  letI : IsFiniteMeasure (ξ.toMeasure.restrict W.carrier) :=
    ⟨by simpa using (window_measure_lt_top ℝ≥0 ξ.toMeasure W)⟩
  exact clusterMeasure_integral_of_integrable_pairings F D (ξ.toMeasure.restrict W.carrier)
    (fun f => testPairingNN_integrable F D f _) f

end WP.Critical.PantsCluster
