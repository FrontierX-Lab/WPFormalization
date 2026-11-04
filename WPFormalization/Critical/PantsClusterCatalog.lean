import WPFormalization.Critical.PantsClusterContinuity

/-! Finite relevant marked catalogs on compact positive-waist families and
exact support tests for the actual full primitive counting measure.  A
waist-to-curve filling bound is deliberately not assumed or asserted here. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter
open scoped Topology ENNReal NNReal CompactlySupported

variable (F : Family.{u,v})

lemma compact_finite_catalog (D : DeformationClassics F)
    (K : Set Waist) (hK : IsCompact K) (L : ℝ) :
    ∃ S : Finset F.Primitive, ∀ s ∈ K, ∀ γ : F.Primitive,
      F.length s γ ≤ L → γ ∈ S := by
  classical
  let U : Waist → Set Waist := fun t => {s | ∀ γ : F.Primitive, F.length t γ ≤ 2 * F.length s γ}
  obtain ⟨T,hTK,hcover⟩ := hK.elim_nhds_subcover U
    (fun t _ => local_length_comparison F D t)
  refine ⟨T.biUnion (fun t => F.short t (2*L)), ?_⟩
  intro s hs γ hγ
  obtain ⟨t,htT,hts⟩ := Set.mem_iUnion₂.mp (hcover hs)
  apply Finset.mem_biUnion.mpr
  refine ⟨t,htT,(F.mem_short t _ _).mpr ?_⟩
  exact (hts γ).trans (mul_le_mul_of_nonneg_left hγ (by norm_num))

lemma measure_window_eq_zero_iff (s : Waist) (B : Set ℝ≥0) (hB : MeasurableSet B) :
    measure F s B = 0 ↔ ∀ γ : F.Primitive, Real.toNNReal (F.length s γ) ∉ B := by
  rw [measure,Measure.sum_apply _ hB,ENNReal.tsum_eq_zero]
  constructor
  · intro h γ hγ
    simpa [Measure.dirac_apply' _ hB,hγ] using h γ
  · intro h γ
    simp [Measure.dirac_apply' _ hB,h γ]

lemma measure_prefix_eq_zero_iff (s : Waist) (L : ℝ≥0) :
    measure F s (Iic L) = 0 ↔ ∀ γ : F.Primitive, (L : ℝ) < F.length s γ := by
  rw [measure_window_eq_zero_iff F s _ measurableSet_Iic]
  simp only [Set.mem_Iic,Real.toNNReal_le_iff_le_coe,not_le]

lemma restricted_prefix_eq_zero_iff (s : Waist) (L : ℝ≥0) :
    (measure F s).restrict (Iic L) = 0 ↔ ∀ γ : F.Primitive, (L : ℝ) < F.length s γ := by
  rw [Measure.restrict_eq_zero,measure_prefix_eq_zero_iff]

def remainderMeasure (s : Waist) : Measure ℝ≥0 :=
  Measure.sum (fun γ : ↥({F.waistClass} : Set F.Primitive)ᶜ =>
    Measure.dirac (Real.toNNReal (F.length s γ.val)))

lemma measure_eq_waist_add_remainder (s : Waist) :
    measure F s = Measure.dirac (Real.toNNReal s.val) + remainderMeasure F s := by
  classical
  let μ : F.Primitive → Measure ℝ≥0 := fun γ => Measure.dirac (Real.toNNReal (F.length s γ))
  have hs : Measure.sum (fun γ : ({F.waistClass} : Set F.Primitive) => μ γ.val) =
      Measure.dirac (Real.toNNReal s.val) := by
    letI : Unique ↥({F.waistClass} : Set F.Primitive) :=
      { default := ⟨F.waistClass,by simp⟩
        uniq := fun γ => Subtype.ext (Set.mem_singleton_iff.mp γ.property) }
    ext B hB
    rw [Measure.sum_apply _ hB,tsum_fintype]
    simp [μ,Family.length_waist]
  have hh := Measure.sum_add_sum_compl ({F.waistClass} : Set F.Primitive) μ
  rw [hs] at hh
  exact hh.symm

end WP.Critical.PantsCluster
