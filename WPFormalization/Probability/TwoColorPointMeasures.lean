import WPFormalization.Probability.NNRealWindowBasis
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-! Two genuine half-line counting measures, encoded on the disjoint union.
The first color is the nonseparating process, the second the pants process.
This is pure measure theory and contains no geometric moment hypothesis. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set Topology
open scoped Topology CompactlySupported ENNReal NNReal

abbrev TwoColorSpace := ℝ≥0 ⊕ ℝ≥0
abbrev TwoColorPointMeasure := PointMeasure ℝ≥0 × PointMeasure ℝ≥0

instance twoColorSpace_borel : BorelSpace TwoColorSpace where
  measurable_eq := by
    apply le_antisymm
    · intro B hB
      have hl : MeasurableSet (Sum.inl ⁻¹' B : Set ℝ≥0) := hB.1
      have hr : MeasurableSet (Sum.inr ⁻¹' B : Set ℝ≥0) := hB.2
      letI : MeasurableSpace TwoColorSpace := borel TwoColorSpace
      letI : BorelSpace TwoColorSpace := ⟨rfl⟩
      have hleft : MeasurableSet (Sum.inl '' (Sum.inl ⁻¹' B : Set ℝ≥0) : Set TwoColorSpace) :=
        (IsOpenEmbedding.inl.measurableEmbedding).measurableSet_image.mpr hl
      have hright : MeasurableSet (Sum.inr '' (Sum.inr ⁻¹' B : Set ℝ≥0) : Set TwoColorSpace) :=
        (IsOpenEmbedding.inr.measurableEmbedding).measurableSet_image.mpr hr
      have he : B=Sum.inl '' (Sum.inl ⁻¹' B : Set ℝ≥0) ∪ Sum.inr '' (Sum.inr ⁻¹' B : Set ℝ≥0) := by
        ext z
        cases z <;> simp
      rw [he]
      exact hleft.union hright
    · apply MeasurableSpace.generateFrom_le
      intro B hB
      exact ⟨(hB.preimage continuous_inl).measurableSet,(hB.preimage continuous_inr).measurableSet⟩

instance twoColorSpace_locallyCompact : LocallyCompactSpace TwoColorSpace where
  local_compact_nhds := by
    intro z U hU
    cases z with
    | inl x =>
      have hp : Sum.inl ⁻¹' U ∈ 𝓝 x := continuous_inl.continuousAt hU
      obtain ⟨K,hK,hKU,hc⟩ := local_compact_nhds hp
      exact ⟨Sum.inl '' K,IsOpenEmbedding.inl.image_mem_nhds.mpr hK,
        image_subset_iff.mpr hKU,hc.image continuous_inl⟩
    | inr x =>
      have hp : Sum.inr ⁻¹' U ∈ 𝓝 x := continuous_inr.continuousAt hU
      obtain ⟨K,hK,hKU,hc⟩ := local_compact_nhds hp
      exact ⟨Sum.inr '' K,IsOpenEmbedding.inr.image_mem_nhds.mpr hK,
        image_subset_iff.mpr hKU,hc.image continuous_inr⟩

def twoColorMeasure (μ ν : Measure ℝ≥0) : Measure TwoColorSpace :=
  Measure.map Sum.inl μ + Measure.map Sum.inr ν

lemma twoColorMeasure_apply (μ ν : Measure ℝ≥0) (B : Set TwoColorSpace)
    (hB : MeasurableSet B) :
    twoColorMeasure μ ν B = μ (Sum.inl ⁻¹' B)+ν (Sum.inr ⁻¹' B) := by
  rw [twoColorMeasure,Measure.add_apply,Measure.map_apply measurable_inl hB,
    Measure.map_apply measurable_inr hB]

lemma twoColorMeasure_inl (μ ν : Measure ℝ≥0) (B : Set ℝ≥0) (hB : MeasurableSet B) :
    twoColorMeasure μ ν (Sum.inl '' B) = μ B := by
  rw [twoColorMeasure_apply μ ν _ (MeasurableSet.inl_image hB)]
  simp [Sum.inl_injective.preimage_image]

lemma twoColorMeasure_inr (μ ν : Measure ℝ≥0) (B : Set ℝ≥0) (hB : MeasurableSet B) :
    twoColorMeasure μ ν (Sum.inr '' B) = ν B := by
  rw [twoColorMeasure_apply μ ν _ (MeasurableSet.inr_image hB)]
  simp [Sum.inr_injective.preimage_image]

instance twoColorMeasure_locallyFinite (μ ν : Measure ℝ≥0)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (twoColorMeasure μ ν) := by
  constructor
  intro z
  cases z with
  | inl x =>
    refine ⟨Sum.inl '' Iic (x+1),IsOpenEmbedding.inl.image_mem_nhds.mpr (Iic_mem_nhds (by simp)),?_⟩
    rw [twoColorMeasure_inl μ ν _ measurableSet_Iic]
    exact window_measure_lt_top ℝ≥0 μ (nnrealPrefixWindow (x+1))
  | inr x =>
    refine ⟨Sum.inr '' Iic (x+1),IsOpenEmbedding.inr.image_mem_nhds.mpr (Iic_mem_nhds (by simp)),?_⟩
    rw [twoColorMeasure_inr μ ν _ measurableSet_Iic]
    exact window_measure_lt_top ℝ≥0 ν (nnrealPrefixWindow (x+1))

instance twoColorMeasure_regular (μ ν : Measure ℝ≥0)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] :
    Measure.Regular (twoColorMeasure μ ν) := by infer_instance

lemma twoColor_preimage_inl_compactClosure (B : Set TwoColorSpace)
    (hB : IsCompact (closure B)) : IsCompact (closure (Sum.inl ⁻¹' B)) :=
  (IsClosedEmbedding.inl.isCompact_preimage hB).of_isClosed_subset isClosed_closure
    (continuous_inl.closure_preimage_subset B)

lemma twoColor_preimage_inr_compactClosure (B : Set TwoColorSpace)
    (hB : IsCompact (closure B)) : IsCompact (closure (Sum.inr ⁻¹' B)) :=
  (IsClosedEmbedding.inr.isCompact_preimage hB).of_isClosed_subset isClosed_closure
    (continuous_inr.closure_preimage_subset B)

/-- The actual direct sum of two locally finite Radon integer measures. -/
def twoColorEncode (ξ : TwoColorPointMeasure) : PointMeasure TwoColorSpace where
  toMeasure := twoColorMeasure ξ.1.toMeasure ξ.2.toMeasure
  locallyFinite := inferInstance
  regular := inferInstance
  integerOnRelCompact := by
    intro B hB hc
    obtain ⟨n,hn⟩ := ξ.1.integerOnRelCompact (Sum.inl ⁻¹' B) (hB.preimage measurable_inl)
      (twoColor_preimage_inl_compactClosure B hc)
    obtain ⟨m,hm⟩ := ξ.2.integerOnRelCompact (Sum.inr ⁻¹' B) (hB.preimage measurable_inr)
      (twoColor_preimage_inr_compactClosure B hc)
    exact ⟨n+m,by rw [twoColorMeasure_apply _ _ B hB,hn,hm,Nat.cast_add]⟩

/-- The corresponding window in the first clopen color component. -/
def twoColorLeftWindow (B : RelCompactBorelWindow ℝ≥0) : RelCompactBorelWindow TwoColorSpace where
  carrier := Sum.inl '' B.carrier
  measurableSet := B.measurableSet.inl_image
  compactClosure := by
    have he : closure (Sum.inl '' B.carrier)=Sum.inl '' closure B.carrier :=
      (IsClosedEmbedding.inl : IsClosedEmbedding (Sum.inl : ℝ≥0 → TwoColorSpace)).closure_image_eq B.carrier
    rw [he]
    exact B.compactClosure.image continuous_inl

def twoColorRightWindow (B : RelCompactBorelWindow ℝ≥0) : RelCompactBorelWindow TwoColorSpace where
  carrier := Sum.inr '' B.carrier
  measurableSet := B.measurableSet.inr_image
  compactClosure := by
    have he : closure (Sum.inr '' B.carrier)=Sum.inr '' closure B.carrier :=
      (IsClosedEmbedding.inr : IsClosedEmbedding (Sum.inr : ℝ≥0 → TwoColorSpace)).closure_image_eq B.carrier
    rw [he]
    exact B.compactClosure.image continuous_inr

lemma twoColorEncode_count_left (ξ : TwoColorPointMeasure) (B : RelCompactBorelWindow ℝ≥0) :
    (twoColorEncode ξ).count TwoColorSpace (twoColorLeftWindow B)=ξ.1.count ℝ≥0 B := by
  have hh := (twoColorEncode ξ).count_spec TwoColorSpace (twoColorLeftWindow B)
  change twoColorMeasure ξ.1.toMeasure ξ.2.toMeasure (Sum.inl '' B.carrier)=_ at hh
  rw [twoColorMeasure_inl _ _ _ B.measurableSet,ξ.1.count_spec ℝ≥0 B] at hh
  exact_mod_cast hh.symm

lemma twoColorEncode_count_right (ξ : TwoColorPointMeasure) (B : RelCompactBorelWindow ℝ≥0) :
    (twoColorEncode ξ).count TwoColorSpace (twoColorRightWindow B)=ξ.2.count ℝ≥0 B := by
  have hh := (twoColorEncode ξ).count_spec TwoColorSpace (twoColorRightWindow B)
  change twoColorMeasure ξ.1.toMeasure ξ.2.toMeasure (Sum.inr '' B.carrier)=_ at hh
  rw [twoColorMeasure_inr _ _ _ B.measurableSet,ξ.2.count_spec ℝ≥0 B] at hh
  exact_mod_cast hh.symm

end WP.Probability
