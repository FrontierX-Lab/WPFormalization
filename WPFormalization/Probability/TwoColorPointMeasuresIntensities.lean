import WPFormalization.Probability.TwoColorPointMeasures
import WPFormalization.Critical.SurvivingMixedVolumeMeasures

/-! The original physical intensities on the genuine nonnegative length line.
Comapping the inclusion preserves physical lengths and the original masses. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set Topology
open scoped Topology ENNReal NNReal

instance criticalIntensity_locallyFinite (c : ℝ) : IsLocallyFiniteMeasure (criticalIntensity c) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (Critical.surviving_criticalIntensityDensity_continuous c)

instance tightIntensity_locallyFinite : IsLocallyFiniteMeasure tightIntensity :=
  IsLocallyFiniteMeasure.withDensity_ofReal Critical.surviving_tightIntensityDensity_continuous

instance criticalIntensity_regular (c : ℝ) : Measure.Regular (criticalIntensity c) := by infer_instance
instance tightIntensity_regular : Measure.Regular tightIntensity := by infer_instance
instance criticalIntensity_nullSingleton (c : ℝ) : NullSingletonClass (criticalIntensity c) := by
  unfold criticalIntensity
  infer_instance
instance tightIntensity_nullSingleton : NullSingletonClass tightIntensity := by
  unfold tightIntensity
  infer_instance

/-- The same physical intensity on NNReal, via inclusion into the real line. -/
def nonnegativeIntensity (ν : Measure ℝ) : Measure ℝ≥0 := Measure.comap NNReal.toReal ν

lemma nonnegativeIntensity_apply (ν : Measure ℝ) (B : Set ℝ≥0) :
    nonnegativeIntensity ν B=ν (NNReal.toReal '' B) :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply ν B

instance nonnegativeIntensity_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (nonnegativeIntensity ν) := by
  constructor
  intro x
  refine ⟨Iic (x+1),Iic_mem_nhds (by simp),?_⟩
  rw [nonnegativeIntensity_apply]
  have hc : IsCompact (Iic (x+1):Set ℝ≥0) := by
    have he : Iic (x+1)=Icc (0:ℝ≥0) (x+1) := by ext t;simp
    rw [he]
    exact isCompact_Icc
  exact (hc.image NNReal.continuous_coe).measure_lt_top

instance nonnegativeIntensity_regular (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    Measure.Regular (nonnegativeIntensity ν) := by infer_instance

instance nonnegativeIntensity_nullSingleton (ν : Measure ℝ) [NullSingletonClass ν] :
    NullSingletonClass (nonnegativeIntensity ν) := by
  constructor
  intro x
  rw [nonnegativeIntensity_apply,Set.image_singleton,measure_singleton]

/-- Nonseparating simple curves have the physical intensity ν. -/
def nonseparatingLengthIntensity : Measure ℝ≥0 := nonnegativeIntensity tightIntensity
/-- Two-cusp pants have the physical critical intensity μ_c. -/
def criticalPantsLengthIntensity (c : ℝ) : Measure ℝ≥0 := nonnegativeIntensity (criticalIntensity c)
/-- ν on the left component and μ_c on the right component. -/
def criticalTwoColorIntensity (c : ℝ) : Measure TwoColorSpace :=
  twoColorMeasure nonseparatingLengthIntensity (criticalPantsLengthIntensity c)

instance nonseparatingLengthIntensity_locallyFinite : IsLocallyFiniteMeasure nonseparatingLengthIntensity :=
  inferInstanceAs (IsLocallyFiniteMeasure (nonnegativeIntensity tightIntensity))
instance criticalPantsLengthIntensity_locallyFinite (c : ℝ) : IsLocallyFiniteMeasure (criticalPantsLengthIntensity c) :=
  inferInstanceAs (IsLocallyFiniteMeasure (nonnegativeIntensity (criticalIntensity c)))
instance nonseparatingLengthIntensity_regular : Measure.Regular nonseparatingLengthIntensity :=
  inferInstanceAs (Measure.Regular (nonnegativeIntensity tightIntensity))
instance criticalPantsLengthIntensity_regular (c : ℝ) : Measure.Regular (criticalPantsLengthIntensity c) :=
  inferInstanceAs (Measure.Regular (nonnegativeIntensity (criticalIntensity c)))
instance nonseparatingLengthIntensity_nullSingleton : NullSingletonClass nonseparatingLengthIntensity :=
  inferInstanceAs (NullSingletonClass (nonnegativeIntensity tightIntensity))
instance criticalPantsLengthIntensity_nullSingleton (c : ℝ) : NullSingletonClass (criticalPantsLengthIntensity c) :=
  inferInstanceAs (NullSingletonClass (nonnegativeIntensity (criticalIntensity c)))
instance criticalTwoColorIntensity_locallyFinite (c : ℝ) : IsLocallyFiniteMeasure (criticalTwoColorIntensity c) :=
  inferInstanceAs (IsLocallyFiniteMeasure (twoColorMeasure nonseparatingLengthIntensity (criticalPantsLengthIntensity c)))
instance criticalTwoColorIntensity_regular (c : ℝ) : Measure.Regular (criticalTwoColorIntensity c) :=
  inferInstanceAs (Measure.Regular (twoColorMeasure nonseparatingLengthIntensity (criticalPantsLengthIntensity c)))

lemma nonnegativeIntensity_window_image_measurable (B : Set ℝ≥0) (hB : MeasurableSet B) :
    MeasurableSet (NNReal.toReal '' B) :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hB

lemma nonnegativeIntensity_window_image_bound (B : Set ℝ≥0) (L : ℝ≥0) (hB : B ⊆ Iic L) :
    NNReal.toReal '' B ⊆ Icc 0 (L:ℝ) := by
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨x.2,by exact_mod_cast hB hx⟩

lemma nonseparatingLengthIntensity_toReal (B : Set ℝ≥0) (hB : MeasurableSet B)
    (L : ℝ≥0) (hBL : B ⊆ Iic L) :
    (nonseparatingLengthIntensity B).toReal = ∫ t in NNReal.toReal '' B,tightIntensityDensity t := by
  rw [nonseparatingLengthIntensity,nonnegativeIntensity_apply]
  exact Critical.surviving_tightIntensity_toReal _
    (nonnegativeIntensity_window_image_measurable B hB) L
    (nonnegativeIntensity_window_image_bound B L hBL)

lemma criticalPantsLengthIntensity_toReal (c : ℝ) (B : Set ℝ≥0) (hB : MeasurableSet B)
    (L : ℝ≥0) (hBL : B ⊆ Iic L) :
    (criticalPantsLengthIntensity c B).toReal = ∫ s in NNReal.toReal '' B,criticalIntensityDensity c s := by
  rw [criticalPantsLengthIntensity,nonnegativeIntensity_apply]
  exact Critical.surviving_criticalIntensity_toReal c _
    (nonnegativeIntensity_window_image_measurable B hB) L
    (nonnegativeIntensity_window_image_bound B L hBL)

/-- The exact (G.6) contribution expressed in the actual NNReal intensities
used by the joint point-process criterion, with no scaling of lengths. -/
lemma surviving_mixed_nnreal_contribution_tendsto (P : PsiTheory) (n : ℕ → ℕ)
    (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ≥0) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ≥0) (hIL : ∀ i,I i ⊆ Iic L) :
    Tendsto (fun g => Critical.survivingMixedCutContribution P g (n g) r k
      (fun i => NNReal.toReal '' I i)) atTop
      (𝓝 ((∏ j : Fin r,(criticalPantsLengthIntensity c (I (Fin.castAdd k j))).toReal) *
        ∏ i : Fin k,(nonseparatingLengthIntensity (I (Fin.natAdd r i))).toReal)) := by
  simp only [criticalPantsLengthIntensity,nonseparatingLengthIntensity,nonnegativeIntensity_apply]
  exact Critical.surviving_mixed_cut_contribution_measure_tendsto P n c hc hn r k _
    (fun i => nonnegativeIntensity_window_image_measurable (I i) (hI i)) L L.2
    (fun i => nonnegativeIntensity_window_image_bound (I i) L (hIL i))

end WP.Probability
