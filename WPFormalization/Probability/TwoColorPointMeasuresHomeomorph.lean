import WPFormalization.Probability.TwoColorPointMeasuresTopology

/-! The pair and disjoint-union encodings have exactly the same genuine
compact-test vague topology. The projections are actual point measures. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set Topology
open scoped Topology CompactlySupported ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

private lemma pointMeasure_eq_of_measure_eq {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    {ξ η : PointMeasure E} (h : ξ.toMeasure=η.toMeasure) : ξ=η := by
  cases ξ;cases η;cases h;rfl

def twoColorLeftProjection (ξ : PointMeasure TwoColorSpace) : PointMeasure ℝ≥0 where
  toMeasure := ξ.toMeasure.comap Sum.inl
  locallyFinite := by
    constructor
    intro x
    obtain ⟨U,hU,hfin⟩ := ξ.locallyFinite.finiteAtNhds (Sum.inl x)
    refine ⟨Sum.inl ⁻¹' U,continuous_inl.continuousAt hU,?_⟩
    rw [IsOpenEmbedding.inl.measurableEmbedding.comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt hfin
  regular := by
    have hl : IsLocallyFiniteMeasure (ξ.toMeasure.comap (Sum.inl : ℝ≥0 → TwoColorSpace)) := by
      constructor
      intro x
      obtain ⟨U,hU,hfin⟩ := ξ.locallyFinite.finiteAtNhds (Sum.inl x)
      refine ⟨Sum.inl ⁻¹' U,continuous_inl.continuousAt hU,?_⟩
      rw [IsOpenEmbedding.inl.measurableEmbedding.comap_apply]
      exact (measure_mono (image_preimage_subset _ _)).trans_lt hfin
    letI := hl
    infer_instance
  integerOnRelCompact := by
    intro B hB hc
    rw [IsOpenEmbedding.inl.measurableEmbedding.comap_apply]
    exact ξ.integerOnRelCompact _ hB.inl_image (twoColorLeftWindow ⟨B,hB,hc⟩).compactClosure

def twoColorRightProjection (ξ : PointMeasure TwoColorSpace) : PointMeasure ℝ≥0 where
  toMeasure := ξ.toMeasure.comap Sum.inr
  locallyFinite := by
    constructor
    intro x
    obtain ⟨U,hU,hfin⟩ := ξ.locallyFinite.finiteAtNhds (Sum.inr x)
    refine ⟨Sum.inr ⁻¹' U,continuous_inr.continuousAt hU,?_⟩
    rw [IsOpenEmbedding.inr.measurableEmbedding.comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt hfin
  regular := by
    have hl : IsLocallyFiniteMeasure (ξ.toMeasure.comap (Sum.inr : ℝ≥0 → TwoColorSpace)) := by
      constructor
      intro x
      obtain ⟨U,hU,hfin⟩ := ξ.locallyFinite.finiteAtNhds (Sum.inr x)
      refine ⟨Sum.inr ⁻¹' U,continuous_inr.continuousAt hU,?_⟩
      rw [IsOpenEmbedding.inr.measurableEmbedding.comap_apply]
      exact (measure_mono (image_preimage_subset _ _)).trans_lt hfin
    letI := hl
    infer_instance
  integerOnRelCompact := by
    intro B hB hc
    rw [IsOpenEmbedding.inr.measurableEmbedding.comap_apply]
    exact ξ.integerOnRelCompact _ hB.inr_image (twoColorRightWindow ⟨B,hB,hc⟩).compactClosure

def twoColorDecode (ξ : PointMeasure TwoColorSpace) : TwoColorPointMeasure :=
  (twoColorLeftProjection ξ,twoColorRightProjection ξ)

lemma twoColorLeftProjection_count (ξ : PointMeasure TwoColorSpace) (B : RelCompactBorelWindow ℝ≥0) :
    (twoColorLeftProjection ξ).count ℝ≥0 B=ξ.count TwoColorSpace (twoColorLeftWindow B) := by
  have hh := (twoColorLeftProjection ξ).count_spec ℝ≥0 B
  change ξ.toMeasure.comap Sum.inl B.carrier=_ at hh
  rw [IsOpenEmbedding.inl.measurableEmbedding.comap_apply] at hh
  change ξ.toMeasure (twoColorLeftWindow B).carrier=_ at hh
  rw [ξ.count_spec TwoColorSpace _] at hh
  exact_mod_cast hh.symm

lemma twoColorRightProjection_count (ξ : PointMeasure TwoColorSpace) (B : RelCompactBorelWindow ℝ≥0) :
    (twoColorRightProjection ξ).count ℝ≥0 B=ξ.count TwoColorSpace (twoColorRightWindow B) := by
  have hh := (twoColorRightProjection ξ).count_spec ℝ≥0 B
  change ξ.toMeasure.comap Sum.inr B.carrier=_ at hh
  rw [IsOpenEmbedding.inr.measurableEmbedding.comap_apply] at hh
  change ξ.toMeasure (twoColorRightWindow B).carrier=_ at hh
  rw [ξ.count_spec TwoColorSpace _] at hh
  exact_mod_cast hh.symm

lemma twoColorDecode_encode (ξ : TwoColorPointMeasure) : twoColorDecode (twoColorEncode ξ)=ξ := by
  apply Prod.ext
  · apply pointMeasure_eq_of_measure_eq
    ext B hB
    change (twoColorMeasure ξ.1.toMeasure ξ.2.toMeasure).comap Sum.inl B=_
    rw [IsOpenEmbedding.inl.measurableEmbedding.comap_apply,twoColorMeasure_inl _ _ _ hB]
  · apply pointMeasure_eq_of_measure_eq
    ext B hB
    change (twoColorMeasure ξ.1.toMeasure ξ.2.toMeasure).comap Sum.inr B=_
    rw [IsOpenEmbedding.inr.measurableEmbedding.comap_apply,twoColorMeasure_inr _ _ _ hB]

lemma twoColorEncode_decode (ξ : PointMeasure TwoColorSpace) : twoColorEncode (twoColorDecode ξ)=ξ := by
  apply pointMeasure_eq_of_measure_eq
  ext B hB
  change twoColorMeasure (ξ.toMeasure.comap Sum.inl) (ξ.toMeasure.comap Sum.inr) B=ξ.toMeasure B
  rw [twoColorMeasure_apply _ _ _ hB,
    IsOpenEmbedding.inl.measurableEmbedding.comap_apply,
    IsOpenEmbedding.inr.measurableEmbedding.comap_apply]
  have he : B=Sum.inl '' (Sum.inl ⁻¹' B) ∪ Sum.inr '' (Sum.inr ⁻¹' B) := by
    ext z;cases z <;> simp
  have hd : Disjoint (Sum.inl '' (Sum.inl ⁻¹' B)) (Sum.inr '' (Sum.inr ⁻¹' B)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
    cases hxy
  exact (measure_union hd ((hB.preimage measurable_inr).inr_image)).symm.trans
    (congrArg ξ.toMeasure he.symm)

def twoColorLeftTest (f : C_c(ℝ≥0,ℝ)) : C_c(TwoColorSpace,ℝ) where
  toFun := Sum.elim f (fun _ => 0)
  continuous_toFun := continuous_sumElim.mpr ⟨f.continuous,continuous_const⟩
  hasCompactSupport' := by
    have he : Function.support (Sum.elim f (fun _ : ℝ≥0 => (0:ℝ)))=Sum.inl '' Function.support f := by
      ext z;cases z <;> simp [Function.mem_support]
    unfold HasCompactSupport tsupport
    rw [he,IsClosedEmbedding.inl.closure_image_eq]
    exact f.hasCompactSupport.image continuous_inl

def twoColorRightTest (f : C_c(ℝ≥0,ℝ)) : C_c(TwoColorSpace,ℝ) where
  toFun := Sum.elim (fun _ => 0) f
  continuous_toFun := continuous_sumElim.mpr ⟨continuous_const,f.continuous⟩
  hasCompactSupport' := by
    have he : Function.support (Sum.elim (fun _ : ℝ≥0 => (0:ℝ)) f)=Sum.inr '' Function.support f := by
      ext z;cases z <;> simp [Function.mem_support]
    unfold HasCompactSupport tsupport
    rw [he,IsClosedEmbedding.inr.closure_image_eq]
    exact f.hasCompactSupport.image continuous_inr

lemma twoColorLeftProjection_integral (ξ : PointMeasure TwoColorSpace) (f : C_c(ℝ≥0,ℝ)) :
    (∫ x,f x ∂(twoColorLeftProjection ξ).toMeasure)=∫ z,twoColorLeftTest f z ∂ξ.toMeasure := by
  have hh := twoColorEncode_integral (twoColorDecode ξ) (twoColorLeftTest f)
  rw [twoColorEncode_decode] at hh
  change (∫ z,twoColorLeftTest f z ∂ξ.toMeasure)=
    (∫ x,f x ∂(twoColorLeftProjection ξ).toMeasure)+∫ _ : ℝ≥0,(0:ℝ) ∂(twoColorRightProjection ξ).toMeasure at hh
  simpa only [integral_zero,add_zero] using hh.symm

lemma twoColorRightProjection_integral (ξ : PointMeasure TwoColorSpace) (f : C_c(ℝ≥0,ℝ)) :
    (∫ x,f x ∂(twoColorRightProjection ξ).toMeasure)=∫ z,twoColorRightTest f z ∂ξ.toMeasure := by
  have hh := twoColorEncode_integral (twoColorDecode ξ) (twoColorRightTest f)
  rw [twoColorEncode_decode] at hh
  change (∫ z,twoColorRightTest f z ∂ξ.toMeasure)=
    (∫ _ : ℝ≥0,(0:ℝ) ∂(twoColorLeftProjection ξ).toMeasure)+∫ x,f x ∂(twoColorRightProjection ξ).toMeasure at hh
  simpa only [integral_zero,zero_add] using hh.symm

lemma twoColorLeftProjection_continuous : Continuous twoColorLeftProjection := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  simp only [Function.comp_def,twoColorLeftProjection_integral]
  exact pointMeasure_vague_test_continuous (twoColorLeftTest f)

lemma twoColorRightProjection_continuous : Continuous twoColorRightProjection := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  simp only [Function.comp_def,twoColorRightProjection_integral]
  exact pointMeasure_vague_test_continuous (twoColorRightTest f)

lemma twoColorDecode_continuous : Continuous twoColorDecode :=
  twoColorLeftProjection_continuous.prodMk twoColorRightProjection_continuous

/-- An actual homeomorphism for the original compact-support-integral vague
topologies, rather than an assumed identification of convergence criteria. -/
def twoColorHomeomorph : TwoColorPointMeasure ≃ₜ PointMeasure TwoColorSpace where
  toFun := twoColorEncode
  invFun := twoColorDecode
  left_inv := twoColorDecode_encode
  right_inv := twoColorEncode_decode
  continuous_toFun := twoColorEncode_continuous
  continuous_invFun := twoColorDecode_continuous

end WP.Probability
