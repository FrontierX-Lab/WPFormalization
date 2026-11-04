import WPFormalization.RandomGeometry.GenericMarkedCurveLengthPointMeasure
import WPFormalization.RandomGeometry.GeneralPlanarCurveTypes
import WPFormalization.RandomGeometry.GeneralPlanarWindowPointCounts
import WPFormalization.RandomGeometry.GeneralPlanarDensityBasis

/-! The actual planar primitive length process, marked by the number of cusps
on its genus-zero side. All marks come from the same geometric curve catalog. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def generalPlanarMarkedLengthPointProcess (X : G.Moduli g n (fun _=>0)) :
    PointMeasure (ℝ≥0×ℕ) :=
  genericMarkedCurveLengthPointMeasure H X (pantsLengthScale g n)
    (pantsLengthScale_pos g n) (IsPlanarPrimitive H) (planarPrimitiveCuspType H)

lemma generalPlanarMarkedLengthPointProcess_rectangle (X : G.Moduli g n (fun _=>0))
    (B : RelCompactBorelWindow ℝ≥0) (k : ℕ) :
    (generalPlanarMarkedLengthPointProcess H X).toMeasure (generalPlanarTypeWindow k B).carrier=
      (planarLengthPointMeasure H X (pantsLengthScale g n) (pantsLengthScale_pos g n) k).toMeasure B.carrier := by
  change genericMarkedCurveLengthMeasure H X _ _ _ (B.carrier×ˢ{k})=_
  rw [genericMarkedCurveLengthMeasure_rectangle_eq_filtered H X _ (pantsLengthScale_pos g n)
    _ _ B.carrier B.measurableSet (B.compactClosure.bddAbove.mono subset_closure) k]
  simp_rw [planarPrimitiveCuspType_spec]
  rfl

lemma generalPlanarMarkedLengthPointProcess_rectangle_count (X : G.Moduli g n (fun _=>0))
    (B : RelCompactBorelWindow ℝ≥0) (k : ℕ) :
    (generalPlanarMarkedLengthPointProcess H X).count (ℝ≥0×ℕ) (generalPlanarTypeWindow k B)=
      (planarLengthPointMeasure H X (pantsLengthScale g n) (pantsLengthScale_pos g n) k).count ℝ≥0 B := by
  apply Nat.cast_injective (R:=ℝ≥0∞)
  rw [←PointMeasure.count_spec,←PointMeasure.count_spec]
  exact generalPlanarMarkedLengthPointProcess_rectangle H X B k

lemma generalPlanarMarkedLengthPointProcess_rational_count_measurable (k : ℕ) (a b : ℚ) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (generalPlanarMarkedLengthPointProcess H X).count (ℝ≥0×ℕ)
        (generalPlanarTypeWindow k (nnrealRationalWindow a b))) := by
  simp_rw [generalPlanarMarkedLengthPointProcess_rectangle_count]
  exact generalPlanarLengthPointMeasure_rational_count_measurable H _ (pantsLengthScale_pos g n) k a b

lemma generalPlanarMarkedLengthPointProcess_basis_count_measurable
    (B : RelCompactBorelWindow (ℝ≥0×ℕ)) (hB : B∈generalPlanarRationalWindows) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (generalPlanarMarkedLengthPointProcess H X).count (ℝ≥0×ℕ) B) := by
  obtain ⟨⟨k,a,b⟩,rfl⟩ := hB
  exact generalPlanarMarkedLengthPointProcess_rational_count_measurable H k a b

end WP.RandomGeometry
