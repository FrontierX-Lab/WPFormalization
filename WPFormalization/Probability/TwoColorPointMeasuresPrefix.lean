import WPFormalization.Probability.TwoColorPointMeasuresConvergence

/-! Prefix counts suffice for either color's rational-window measurability.
The case split retains atoms at zero for a general genuine point measure. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

lemma pointMeasure_count_congr {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (ξ : PointMeasure E) (A B : RelCompactBorelWindow E) (h : A.carrier=B.carrier) :
    ξ.count E A=ξ.count E B := by
  have hh : (ξ.count E A:ℝ≥0∞)=(ξ.count E B:ℝ≥0∞) := by
    rw [←ξ.count_spec E A,←ξ.count_spec E B,h]
  exact_mod_cast hh

lemma pointMeasure_count_nnrealRationalWindow (ξ : PointMeasure ℝ≥0) (a b : ℚ) :
    ξ.count ℝ≥0 (nnrealRationalWindow a b)=
      if (b:ℝ)<0 then 0 else if (a:ℝ)<0 then ξ.count ℝ≥0 (nnrealPrefixWindow (Real.toNNReal b)) else
        ξ.count ℝ≥0 (nnrealPrefixWindow (Real.toNNReal b))-
          ξ.count ℝ≥0 (nnrealPrefixWindow (Real.toNNReal a)) := by
  by_cases hb : (b:ℝ)<0
  · rw [if_pos hb]
    apply ξ.count_empty
    ext x
    simp only [mem_nnrealRationalWindow,mem_empty_iff_false,iff_false,not_and]
    intro hax hxb
    exact (not_le_of_gt hb) (x.2.trans hxb)
  · rw [if_neg hb]
    have hb0 : 0 ≤ (b:ℝ) := le_of_not_gt hb
    by_cases ha : (a:ℝ)<0
    · rw [if_pos ha]
      apply pointMeasure_count_congr
      ext x
      simp only [mem_nnrealRationalWindow,nnrealPrefixWindow,mem_Iic]
      have hax : (a:ℝ)<(x:ℝ) := ha.trans_le x.2
      have hx : x ≤ Real.toNNReal (b:ℝ) ↔ (x:ℝ) ≤ b := by
        rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ hb0]
      exact and_iff_right hax |>.trans hx.symm
    · rw [if_neg ha,←ξ.count_nnrealIoc (Real.toNNReal a) (Real.toNNReal b)]
      apply pointMeasure_count_congr
      ext x
      simp only [mem_nnrealRationalWindow,nnrealIocWindow,mem_Ioc]
      rw [←NNReal.coe_lt_coe,←NNReal.coe_le_coe,Real.coe_toNNReal _ (le_of_not_gt ha),Real.coe_toNNReal _ hb0]

lemma aemeasurable_nnrealRationalWindow_counts_of_prefix {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ξ : Ω → PointMeasure ℝ≥0)
    (hcounts : ∀ b : ℝ≥0,AEMeasurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealPrefixWindow b)) μ)
    (a b : ℚ) :
    AEMeasurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealRationalWindow a b)) μ := by
  simp_rw [pointMeasure_count_nnrealRationalWindow]
  split_ifs
  · exact aemeasurable_const
  · exact hcounts _
  · exact (hcounts _).sub (hcounts _)

lemma aemeasurable_nnrealRationalWindows_counts_of_prefix {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ξ : Ω → PointMeasure ℝ≥0)
    (hcounts : ∀ b : ℝ≥0,AEMeasurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealPrefixWindow b)) μ)
    (B : RelCompactBorelWindow ℝ≥0) (hB : B ∈ nnrealRationalWindows) :
    AEMeasurable (fun ω => (Ξ ω).count ℝ≥0 B) μ := by
  obtain ⟨⟨a,b⟩,rfl⟩ := hB
  exact aemeasurable_nnrealRationalWindow_counts_of_prefix μ Ξ hcounts a b

end WP.Probability
