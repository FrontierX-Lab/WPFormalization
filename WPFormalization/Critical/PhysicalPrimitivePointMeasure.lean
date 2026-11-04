import WPFormalization.RandomGeometry.CurveWindowPointCounts
import WPFormalization.External.PointProcessProbability

/- Genuine complete unoriented primitive spectrum at physical scale one.
This includes nonsimple primitive geodesics and preserves multiplicities. -/
noncomputable section
universe u v w
namespace WP.Critical
open WP.External WP.RandomGeometry WP.Probability MeasureTheory Set
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def physicalPrimitiveLengthPointMeasure (X : G.Moduli g n (fun _ => 0)) :
    PointMeasure ℝ≥0 := primitiveLengthPointMeasure H X 1 (by norm_num)

lemma physicalPrimitiveLengthPointMeasure_prefix (X : G.Moduli g n (fun _ => 0))
    (B : ℝ≥0) :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure (Iic B) =
      (H.primitiveCount X B : ℝ≥0∞) := by
  simpa [physicalPrimitiveLengthPointMeasure] using
    primitiveLengthPointMeasure_Iic H X 1 (by norm_num) B

lemma physicalPrimitiveLengthPointMeasure_prefix_count (X : G.Moduli g n (fun _ => 0))
    (B : ℝ≥0) :
    (physicalPrimitiveLengthPointMeasure H X).count ℝ≥0 (nnrealPrefixWindow B) =
      H.primitiveCount X B := by
  simpa [physicalPrimitiveLengthPointMeasure] using
    primitiveLengthPointMeasure_prefix_count H X 1 (by norm_num) B

lemma physicalPrimitiveLengthPointMeasure_singleton_zero
    (X : G.Moduli g n (fun _ => 0)) :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure {0}=0 :=
  curveNNLengthMeasure_singleton_zero H X 1 (by norm_num) _

lemma physicalPrimitiveLengthPointMeasure_prefix_count_measurable (B : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (physicalPrimitiveLengthPointMeasure H X).count ℝ≥0 (nnrealPrefixWindow B)) := by
  simp_rw [physicalPrimitiveLengthPointMeasure_prefix_count]
  exact H.measurable_primitiveCount g n B

lemma physicalPrimitiveLengthPointMeasure_aemeasurable
    (μ : Measure (G.Moduli g n (fun _ => 0))) :
    AEMeasurable (physicalPrimitiveLengthPointMeasure H) μ :=
  pointMeasure_nnreal_aemeasurable_of_prefix_counts μ _
    (fun B => (physicalPrimitiveLengthPointMeasure_prefix_count_measurable H B).aemeasurable)

end WP.Critical
