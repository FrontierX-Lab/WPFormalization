import WPFormalization.RandomGeometry.GeneralPlanarLengthProjectionLaws
import WPFormalization.External.PointProcessProbability

/-! The genuine length projection of all planar cusp types. Finite type
truncations and actual tails establish its count laws before applying the
continuity-semiring criterion for the genuine vague topology. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma generalPlanarLengthPointProcess_singleton_zero {g n : ℕ} (X : G.Moduli g n (fun _=>0)) :
    (generalPlanarLengthPointProcess H X).toMeasure {0}=0 :=
  curveNNLengthMeasure_singleton_zero H X _ (pantsLengthScale_pos g n) _

include C MI in
lemma generalPlanar_length_Ioc_window_count_laws {d : ℕ}
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ≥0) (hab : ∀j,lo j≤hi j)
    (hdis : DisjointWindows ℝ≥0 (fun j=>lengthIocWindow (lo j) (hi j)))
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector ℝ≥0 (fun j=>lengthIocWindow (lo j) (hi j)) (generalPlanarLengthPointProcess H X))
      (productPoissonMeasure (windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l)
        (fun j=>lengthIocWindow (lo j) (hi j)))) id := by
  have he : (fun j=>generalPlanarDensityLengthRate P l (Real.toNNReal ((hi j:ℝ)^2-(lo j:ℝ)^2)))=
      windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l) (fun j=>lengthIocWindow (lo j) (hi j)) := by
    funext j
    have hd : 0≤(hi j:ℝ)^2-(lo j:ℝ)^2 := by
      nlinarith [(lo j).property,(hi j).property,show (lo j:ℝ)≤(hi j:ℝ) from hab j]
    simp only [windowRates,lengthIocWindow,general_planar_density_length_intensity_Ioc,
      ENNReal.ofReal,ENNReal.toNNReal_coe,generalPlanarDensityLengthRate,Real.coe_toNNReal _ hd]
  rw [←he]
  exact generalPlanar_length_Ioc_counts_poisson H T C MI n hn lo hi hab hdis l hl

include C MI in
lemma generalPlanar_length_rational_count_laws {d : ℕ}
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (a b : Fin d→ℚ) (hdis : DisjointWindows ℝ≥0 (fun j=>nnrealRationalWindow (a j) (b j)))
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector ℝ≥0 (fun j=>nnrealRationalWindow (a j) (b j)) (generalPlanarLengthPointProcess H X))
      (productPoissonMeasure (windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l)
        (fun j=>nnrealRationalWindow (a j) (b j)))) id := by
  let lo := fun j=>min (Real.toNNReal (a j)) (Real.toNNReal (b j))
  let hi := fun j=>Real.toNNReal (b j)
  have hvec : (fun g (X : G.Moduli g (n g) (fun _=>0))=>windowCountVector ℝ≥0
      (fun j=>nnrealRationalWindow (a j) (b j)) (generalPlanarLengthPointProcess H X))=
      fun g (X : G.Moduli g (n g) (fun _=>0))=>windowCountVector ℝ≥0
      (fun j=>lengthIocWindow (lo j) (hi j)) (generalPlanarLengthPointProcess H X) := by
    funext g X j
    exact pointMeasure_count_rational_window_eq_canonical_Ioc _
      (generalPlanarLengthPointProcess_singleton_zero H X) (a j) (b j)
  have hr : windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l) (fun j=>nnrealRationalWindow (a j) (b j))=
      windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l) (fun j=>lengthIocWindow (lo j) (hi j)) := by
    funext j
    apply congrArg ENNReal.toNNReal
    exact measure_rational_window_eq_canonical_Ioc _ (measure_singleton _) (a j) (b j)
  rw [hvec,hr]
  exact generalPlanar_length_Ioc_window_count_laws H T C MI n hn lo hi (fun j=>min_le_right _ _)
    (rational_windows_canonical_Ioc_disjoint a b hdis) l hl

include C MI in
lemma generalPlanar_length_semiring_count_laws
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l))
    (d : ℕ) (B : Fin d→RelCompactBorelWindow ℝ≥0)
    (hB : ∀i,B i∈nnrealRationalWindows) (hdis : DisjointWindows ℝ≥0 B) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector ℝ≥0 B (generalPlanarLengthPointProcess H X))
      (productPoissonMeasure (windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l) B)) id := by
  choose ab hab using hB
  have he : B=fun j=>nnrealRationalWindow (ab j).1 (ab j).2 := by
    funext j
    exact (hab j).symm
  subst B
  exact generalPlanar_length_rational_count_laws H T C MI n hn (fun j=>(ab j).1) (fun j=>(ab j).2) hdis l hl

include C MI in
theorem generalPlanar_length_poisson_process
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    ∃Q : ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 (generalPlanarDensityLengthIntensity P l) Q ∧
      LawConverges (fun g=>wpProbability G g (n g))
        (fun g (X : G.Moduli g (n g) (fun _=>0))=>generalPlanarLengthPointProcess H X) Q id := by
  obtain ⟨Q,hQ⟩ := poisson_point_process_exists ℝ≥0 (generalPlanarDensityLengthIntensity P l)
  refine ⟨Q,hQ,?_⟩
  apply pointMeasure_vague_of_semiring_count_laws ℝ≥0 (fun g=>wpProbability G g (n g))
    (fun g (X : G.Moduli g (n g) (fun _=>0))=>generalPlanarLengthPointProcess H X)
    (WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)) ?_
    (generalPlanarDensityLengthIntensity P l) nnrealRationalWindows
    (general_planar_density_length_rational_basis P l) Q hQ
    (generalPlanar_length_semiring_count_laws H T C MI n hn l hl)
  exact Eventually.of_forall (fun g=>pointMeasure_nnreal_aemeasurable_of_prefix_counts _ _
    (fun b=>(generalPlanarLengthPointProcess_prefix_count_measurable H b).aemeasurable))

end WP.RandomGeometry
