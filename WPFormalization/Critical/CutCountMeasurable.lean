import WPFormalization.Critical.CutActualEstimate
noncomputable section
universe aa bb cc dd
namespace WP.Critical.CutGraphOrbits
open WP.External MeasureTheory
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  (MI : MirzakhaniIntegration G H T) {g n k Q : ℕ} (S : CutSkeleton k Q)
include MI in
lemma cutPartitionCount_measurable (u v w : ℕ) (L : ℝ) :
    Measurable (cutPartitionCount T S (g:=g) (n:=n) u v w L) := by
  apply Finset.measurable_sum
  intro o ho
  exact MI.orbitSum_measurable o.val _ (cutLengthTest_measurable k L)
include MI in
lemma cutMarkedPartitionCount_measurable (u v w : ℕ) (L : ℝ) :
    Measurable (cutMarkedPartitionCount T S (g:=g) (n:=n) u v w L) := by
  apply Finset.measurable_sum
  intro o ho
  exact MI.orbitSum_measurable o.val _ (cutLengthTest_measurable k L)
end WP.Critical.CutGraphOrbits
