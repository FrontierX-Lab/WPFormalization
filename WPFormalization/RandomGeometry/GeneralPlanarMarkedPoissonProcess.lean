import WPFormalization.RandomGeometry.GeneralPlanarMarkedMoments
import WPFormalization.External.PointProcessProbability

/-! The actual planar primitive process with its cusp-count mark converges in
the genuine vague topology. This is a component of Theorem 14.1; no assertion
about projection to all lengths or the remaining nonplanar curves is hidden. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma generalPlanarMarkedLengthPointProcess_aemeasurable {g n : ℕ}
    (l : ℝ≥0∞) (μ : Measure (G.Moduli g n (fun _=>0))) :
    AEMeasurable (generalPlanarMarkedLengthPointProcess H) μ := by
  apply pointMeasure_aemeasurable_of_basis_counts (ℝ≥0×ℕ) μ _
    (generalPlanarDensityIntensity P l) generalPlanarRationalWindows
    (general_planar_rational_windows_basis P l)
  intro B hB
  exact (generalPlanarMarkedLengthPointProcess_basis_count_measurable H B hB).aemeasurable

lemma generalPlanarMarkedLengthPointProcess_actual_eventually
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) :
    ∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _=>0),
      (generalPlanarMarkedLengthPointProcess H X).toMeasure=
        Measure.sum (fun γ : {γ : H.Primitive g (n g) X //IsPlanarPrimitive H γ}=>
          Measure.dirac (Real.toNNReal (Real.sqrt (pantsScale g (n g))*H.length γ.val),
            planarPrimitiveCuspType H γ.val)) := by
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hn] with g hg
  intro X
  change genericMarkedCurveLengthMeasure H X _ _ _=_
  rw [hg]
  rfl

include C MI in
theorem generalPlanar_marked_poisson_process
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    ∃Q : ProbabilityMeasure (PointMeasure (ℝ≥0×ℕ)),
      IsPoissonPointProcessLaw (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l) Q ∧
      LawConverges (fun g=>wpProbability G g (n g))
        (fun g (X : G.Moduli g (n g) (fun _=>0))=>generalPlanarMarkedLengthPointProcess H X) Q id := by
  obtain ⟨Q,hQ⟩ := poisson_point_process_exists (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l)
  refine ⟨Q,hQ,?_⟩
  apply pointMeasure_vague_of_semiring_mixed_factorials (ℝ≥0×ℕ)
    (fun g=>wpProbability G g (n g))
    (fun g (X : G.Moduli g (n g) (fun _=>0))=>generalPlanarMarkedLengthPointProcess H X)
    (WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)) ?_
    (generalPlanarDensityIntensity P l) generalPlanarRationalWindows
    (general_planar_rational_windows_basis P l) Q hQ
    (generalPlanar_marked_semiring_mixed_factorials H T C MI n hn l hl)
  exact Eventually.of_forall (fun _=>generalPlanarMarkedLengthPointProcess_aemeasurable H l _)

end WP.RandomGeometry
