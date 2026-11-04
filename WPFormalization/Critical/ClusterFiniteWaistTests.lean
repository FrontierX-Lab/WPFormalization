import WPFormalization.Critical.ClusterMeasurePairings
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

def waistWindow (ε R : ℝ≥0) : RelCompactBorelWindow ℝ≥0 where
  carrier := Icc ε R
  measurableSet := measurableSet_Icc
  compactClosure := by rw [isClosed_Icc.closure_eq];exact isCompact_Icc

def waistTruncatedPairing (f : C_c(ℝ≥0,ℝ)) (ε R : ℝ≥0) : ℝ≥0 → ℝ :=
  (Icc ε R).indicator (testPairingNN F f)

lemma waistTruncatedPairing_measurable (D : DeformationClassics F)
    (f : C_c(ℝ≥0,ℝ)) (ε R : ℝ≥0) :
    Measurable (waistTruncatedPairing F f ε R) :=
  (testPairingNN_measurable F D f).indicator measurableSet_Icc

lemma waistTruncatedPairing_bound (f : C_c(ℝ≥0,ℝ)) (ε R : ℝ≥0) :
    ∃C : ℝ,∀s,‖waistTruncatedPairing F f ε R s‖≤C := by
  obtain ⟨C,hC,hbound⟩ := testPairingNN_uniform_bound F f
  refine ⟨C,fun s => ?_⟩
  by_cases hs : s∈Icc ε R
  · simpa only [waistTruncatedPairing,Set.indicator_of_mem hs] using hbound s
  · simp only [waistTruncatedPairing,Set.indicator_of_notMem hs,norm_zero]
    exact hC.le

lemma waistTruncatedPairing_support (f : C_c(ℝ≥0,ℝ)) (ε R : ℝ≥0) :
    Function.support (waistTruncatedPairing F f ε R) ⊆ Icc ε R := by
  intro s hs
  by_contra hn
  exact hs (Set.indicator_of_notMem hn _)

lemma compactWaistClusterPointMeasure_integral_truncatedPairing (D : DeformationClassics F)
    (ξ : PointMeasure ℝ≥0) (f : C_c(ℝ≥0,ℝ)) (ε R : ℝ≥0) :
    (∫x,f x ∂(compactWaistClusterPointMeasure F D ξ (waistWindow ε R)).toMeasure)=
      ∫s,waistTruncatedPairing F f ε R s ∂ξ.toMeasure := by
  rw [compactWaistClusterPointMeasure_integral]
  exact (integral_indicator measurableSet_Icc).symm

lemma testPairingNN_continuousAt_pos (D : DeformationClassics F)
    (f : C_c(ℝ≥0,ℝ)) (s : ℝ≥0) (hs : 0<s) :
    ContinuousAt (testPairingNN F f) s := by
  let e : Ioi (0:ℝ≥0) → Waist := fun s => ⟨(s.val:ℝ),by exact_mod_cast s.property⟩
  have he : Continuous e := Continuous.subtype_mk
    (NNReal.continuous_coe.comp continuous_subtype_val) _
  have hc : Continuous (fun t : Ioi (0:ℝ≥0) => testPairingNN F f t.val) := by
    convert (test_integral_continuous F D f).comp he using 1
    funext t
    exact testPairingNN_pos F f t.val t.property
  have hco : ContinuousOn (testPairingNN F f) (Ioi (0:ℝ≥0)) :=
    continuousOn_iff_continuous_restrict.mpr hc
  exact hco.continuousAt (isOpen_Ioi.mem_nhds hs)

lemma waistTruncatedPairing_continuousAt (D : DeformationClassics F)
    (f : C_c(ℝ≥0,ℝ)) (ε R s : ℝ≥0) (hε : 0<ε) (hsε : s≠ε) (hsR : s≠R) :
    ContinuousAt (waistTruncatedPairing F f ε R) s := by
  by_cases hlo : s<ε
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ≥0 => (0:ℝ)) s).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hlo] with t ht
    simp only [waistTruncatedPairing,Set.indicator_of_notMem
      (show t∉Icc ε R from fun h => (not_le_of_gt ht) h.1)]
  by_cases hhi : R<s
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ≥0 => (0:ℝ)) s).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hhi] with t ht
    simp only [waistTruncatedPairing,Set.indicator_of_notMem
      (show t∉Icc ε R from fun h => (not_le_of_gt ht) h.2)]
  have hls : ε<s := lt_of_le_of_ne (le_of_not_gt hlo) hsε.symm
  have hsr : s<R := lt_of_le_of_ne (le_of_not_gt hhi) hsR
  apply (testPairingNN_continuousAt_pos F D f s (hε.trans hls)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show s∈Ioo ε R from ⟨hls,hsr⟩)] with t ht
  exact Set.indicator_of_mem (show t∈Icc ε R from ⟨ht.1.le,ht.2.le⟩) (testPairingNN F f)

lemma waistTruncatedPairing_ae_continuousAt (D : DeformationClassics F)
    (f : C_c(ℝ≥0,ℝ)) (ε R : ℝ≥0) (hε : 0<ε)
    (ξ : Measure ℝ≥0) (hξε : ξ {ε}=0) (hξR : ξ {R}=0) :
    ∀ᵐs ∂ξ,ContinuousAt (waistTruncatedPairing F f ε R) s := by
  have hnull : ξ ({ε}∪{R})=0 := by
    apply le_antisymm
    · calc
        ξ ({ε}∪{R}) ≤ ξ {ε}+ξ {R} := measure_union_le _ _
        _ = 0 := by rw [hξε,hξR,add_zero]
    · positivity
  have ha : ∀ᵐs ∂ξ,s∉({ε}∪{R} : Set ℝ≥0) := by
    apply ae_iff.mpr
    change ξ (({ε} ∪ {R} : Set ℝ≥0)ᶜ)ᶜ=0
    rwa [compl_compl]
  filter_upwards [ha] with s hs
  exact waistTruncatedPairing_continuousAt F D f ε R s hε
    (by simpa using (not_or.mp hs).1) (by simpa using (not_or.mp hs).2)

end WP.Critical.PantsCluster
