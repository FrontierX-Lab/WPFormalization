import WPFormalization.Probability.PoissonClusterMeasures
noncomputable section
set_option maxHeartbeats 0
universe u
namespace WP.Probability.PoissonCluster
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Classical
variable {J : Type u} [Countable J]

lemma indexedClusterMeasure_compact_parent_prefix_le (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0)
    (W : RelCompactBorelWindow ℝ≥0) (L : ℝ≥0) (C : ℝ≥0∞)
    (hC : ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C) :
    indexedClusterMeasure length (ξ.toMeasure.restrict W.carrier) (Iic L)≤C*ξ.toMeasure W.carrier := by
  rw [indexedClusterMeasure_apply length hlength _ _ measurableSet_Iic]
  calc
    _≤∫⁻s,C ∂(ξ.toMeasure.restrict W.carrier).restrict (Ioi (0:ℝ≥0)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hC s hs
    _=C*((ξ.toMeasure.restrict W.carrier).restrict (Ioi (0:ℝ≥0))) univ := lintegral_const C
    _≤C*(ξ.toMeasure.restrict W.carrier) univ :=
      mul_le_mul le_rfl (Measure.restrict_apply_le _ _) (by positivity) (by positivity)
    _=C*ξ.toMeasure W.carrier := by simp

lemma indexedClusterMeasure_compact_parent_locallyFinite (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0)
    (W : RelCompactBorelWindow ℝ≥0)
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C) :
    IsLocallyFiniteMeasure (indexedClusterMeasure length (ξ.toMeasure.restrict W.carrier)) := by
  constructor
  intro x
  obtain ⟨C,hC,hbound⟩:=hbound (x+1)
  refine ⟨Iic (x+1),Iic_mem_nhds (by simp),?_⟩
  exact (indexedClusterMeasure_compact_parent_prefix_le length hlength ξ W (x+1) C hbound).trans_lt
    (ENNReal.mul_lt_top hC (window_measure_lt_top ℝ≥0 ξ.toMeasure W))

lemma indexedClusterMeasure_compact_parent_integerOnRelCompact (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0)
    (W : RelCompactBorelWindow ℝ≥0)
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C)
    (B : Set ℝ≥0) (hB : MeasurableSet B) (hcompact : IsCompact (closure B)) :
    ∃n : ℕ,indexedClusterMeasure length (ξ.toMeasure.restrict W.carrier) B=n := by
  letI:=indexedClusterMeasure_compact_parent_locallyFinite length hlength ξ W hbound
  have hfinite : indexedClusterMeasure length (ξ.toMeasure.restrict W.carrier) B<∞ :=
    (measure_mono subset_closure).trans_lt hcompact.measure_lt_top
  have hsum : (∑'γ : J,(((ξ.toMeasure.restrict W.carrier).restrict (Ioi (0:ℝ≥0))).map (length γ)) B)≠∞ := by
    simpa only [indexedClusterMeasure,Measure.sum_apply _ hB] using hfinite.ne
  have hint (γ : J) : ∃n : ℕ,
      (((ξ.toMeasure.restrict W.carrier).restrict (Ioi (0:ℝ≥0))).map (length γ)) B=n := by
    let S : Set ℝ≥0:=((length γ) ⁻¹' B ∩ Ioi (0:ℝ≥0)) ∩ W.carrier
    have hS : MeasurableSet S:=((hB.preimage (hlength γ)).inter measurableSet_Ioi).inter W.measurableSet
    have hSc : IsCompact (closure S) := W.compactClosure.of_isClosed_subset isClosed_closure
      (closure_mono (by intro s hs;exact hs.2))
    obtain ⟨n,hn⟩:=ξ.integerOnRelCompact S hS hSc
    refine ⟨n,?_⟩
    rw [Measure.map_apply (hlength γ) hB,Measure.restrict_apply (hB.preimage (hlength γ)),
      Measure.restrict_apply ((hB.preimage (hlength γ)).inter measurableSet_Ioi)]
    exact hn
  simpa only [indexedClusterMeasure,Measure.sum_apply _ hB] using finite_ennreal_sum_integer hsum hint

def compactParentClusterPointMeasure (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0)
    (W : RelCompactBorelWindow ℝ≥0)
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C) : PointMeasure ℝ≥0 where
  toMeasure:=indexedClusterMeasure length (ξ.toMeasure.restrict W.carrier)
  locallyFinite:=indexedClusterMeasure_compact_parent_locallyFinite length hlength ξ W hbound
  regular:=by
    letI:=indexedClusterMeasure_compact_parent_locallyFinite length hlength ξ W hbound
    infer_instance
  integerOnRelCompact:=indexedClusterMeasure_compact_parent_integerOnRelCompact length hlength ξ W hbound

end WP.Probability.PoissonCluster
