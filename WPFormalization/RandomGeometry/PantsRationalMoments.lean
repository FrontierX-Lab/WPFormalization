import WPFormalization.RandomGeometry.PantsRationalWindows
import WPFormalization.RandomGeometry.PantsPointProcessMoments

/-! All rational continuity-semiring factorial moments of the actual WP
length point process, including windows through zero and empty windows. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
lemma pants_point_process_rational_mixed_factorials (d : ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (a b : Fin d → ℚ)
    (hdis : Pairwise (fun j k => Disjoint (nnrealRationalWindow (a j) (b j)).carrier
      (nnrealRationalWindow (a k) (b k)).carrier)) :
    MixedFactorialMomentLimit (fun g => wpProbability G g (n g))
      (fun g X => windowCountVector ℝ≥0 (fun j => nnrealRationalWindow (a j) (b j))
        (pantsLengthPointProcess H X))
      (windowRates ℝ≥0 quadraticLengthIntensity (fun j => nnrealRationalWindow (a j) (b j))) := by
  let lo := fun j => min (Real.toNNReal (a j)) (Real.toNNReal (b j))
  let hi := fun j => Real.toNNReal (b j)
  have hvec : (fun g (X : G.Moduli g (n g) (fun _ => 0)) =>
      windowCountVector ℝ≥0 (fun j => nnrealRationalWindow (a j) (b j))
        (pantsLengthPointProcess H X)) =
      fun g (X : G.Moduli g (n g) (fun _ => 0)) =>
      windowCountVector ℝ≥0 (fun j => lengthIocWindow (lo j) (hi j))
        (pantsLengthPointProcess H X) := by
    funext g X j
    exact pointMeasure_count_rational_window_eq_canonical_Ioc (pantsLengthPointProcess H X)
      (pantsLengthPointProcess_singleton_zero H X) (a j) (b j)
  have hrates : windowRates ℝ≥0 quadraticLengthIntensity
      (fun j => nnrealRationalWindow (a j) (b j)) =
      windowRates ℝ≥0 quadraticLengthIntensity (fun j => lengthIocWindow (lo j) (hi j)) := by
    funext j
    apply congrArg ENNReal.toNNReal
    exact measure_rational_window_eq_canonical_Ioc _ (measure_singleton _) (a j) (b j)
  rw [hvec,hrates]
  exact pants_point_process_Ioc_mixedFactorialMomentLimit G H T C MI d n hnfast lo hi
    (fun j => min_le_right _ _)
    (rational_windows_canonical_Ioc_disjoint a b hdis)

include C MI in
lemma pants_point_process_semiring_mixed_factorials (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (d : ℕ) (B : Fin d → RelCompactBorelWindow ℝ≥0)
    (hB : ∀i, B i ∈ nnrealRationalWindows) (hdis : DisjointWindows ℝ≥0 B) :
    MixedFactorialMomentLimit (fun g => wpProbability G g (n g))
      (fun g X => windowCountVector ℝ≥0 B (pantsLengthPointProcess H X))
      (windowRates ℝ≥0 quadraticLengthIntensity B) := by
  classical
  choose ab hab using hB
  have he : B=fun j => nnrealRationalWindow (ab j).1 (ab j).2 := by
    funext j
    exact (hab j).symm
  subst B
  exact pants_point_process_rational_mixed_factorials G H T C MI d n hnfast
    (fun j => (ab j).1) (fun j => (ab j).2) hdis

end WP.RandomGeometry
