import WPFormalization.Probability.PoissonClusterDefinitions
import WPFormalization.Probability.TwoColorPointMeasuresTopology
noncomputable section
namespace WP.Probability.PoissonCluster
open MeasureTheory Filter Set
open scoped NNReal Topology CompactlySupported

def pointMeasureLaplaceTest (f : C_c(ℝ≥0,ℝ)) (hf : ∀ x,0≤f x) :
    BoundedContinuousFunction (PointMeasure ℝ≥0) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨laplaceObservable (fun x=>f x),
      Real.continuous_exp.comp (pointMeasure_vague_test_continuous f).neg⟩ 1 (by
        intro ξ η
        have hξ : 0≤laplaceObservable (fun x=>f x) ξ := Real.exp_nonneg _
        have hη : 0≤laplaceObservable (fun x=>f x) η := Real.exp_nonneg _
        have hξ1 : laplaceObservable (fun x=>f x) ξ≤1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integral_nonneg hf))
        have hη1 : laplaceObservable (fun x=>f x) η≤1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integral_nonneg hf))
        change dist (laplaceObservable (fun x=>f x) ξ) (laplaceObservable (fun x=>f x) η)≤1
        rw [Real.dist_eq,abs_le]
        constructor <;> linarith)

lemma pointMeasureLaplaceTest_apply (f : C_c(ℝ≥0,ℝ)) (hf : ∀ x,0≤f x)
    (ξ : PointMeasure ℝ≥0) :
    pointMeasureLaplaceTest f hf ξ=laplaceObservable (fun x=>f x) ξ := rfl

lemma lawConverges_laplaceObservable {Ω : ℕ→Type*} [∀j,MeasurableSpace (Ω j)]
    {Ωlimit : Type*} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ)→Measure (Ω j)) (X : (j : ℕ)→Ω j→PointMeasure ℝ≥0)
    (Q : Measure Ωlimit) (Z : Ωlimit→PointMeasure ℝ≥0)
    (hLaw : LawConverges μ X Q Z) (f : C_c(ℝ≥0,ℝ)) (hf : ∀ x,0≤f x) :
    Tendsto (fun j=>∫ω,laplaceObservable (fun x=>f x) (X j ω) ∂μ j) atTop
      (𝓝 (∫ω,laplaceObservable (fun x=>f x) (Z ω) ∂Q)) :=
  hLaw (pointMeasureLaplaceTest f hf)

end WP.Probability.PoissonCluster
