import WPFormalization.RandomGeometry.PrimitivePlanarWindowComparison
import WPFormalization.RandomGeometry.PrimitiveNonplanarRare
import WPFormalization.RandomGeometry.GeneralPlanarLengthPoissonProcess
import WPFormalization.Probability.LawConvergenceBadEvent

/-! Actual all-primitive bounded-window count laws follow from planar counts
and the locally proved nonplanar rare-event estimate. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def primitiveLengthWindowCounts {g n d : ℕ} (lo hi : Fin d→ℝ≥0)
    (X : G.Moduli g n (fun _=>0)) : Fin d→ℕ :=
  windowCountVector ℝ≥0 (fun j=>lengthIocWindow (lo j) (hi j)) (primitiveLengthPointProcess H X)

lemma primitiveLengthWindowCounts_measurable {g n d : ℕ} (lo hi : Fin d→ℝ≥0) :
    Measurable (primitiveLengthWindowCounts H (g:=g) (n:=n) lo hi) := by
  exact Measurable.of_eval (fun j=>primitiveLengthPointProcess_Ioc_count_measurable H (lo j) (hi j))

def primitivePlanarWindowBad {g n d : ℕ} (lo hi : Fin d→ℝ≥0) : Set (G.Moduli g n (fun _=>0)) :=
  {X |primitiveLengthWindowCounts H lo hi X≠generalPlanarLengthWindowCounts H lo hi X}

lemma primitivePlanarWindowBad_measurable {g n d : ℕ} (lo hi : Fin d→ℝ≥0) :
    MeasurableSet (primitivePlanarWindowBad H (g:=g) (n:=n) lo hi) := by
  exact (measurableSet_eq_fun (primitiveLengthWindowCounts_measurable H lo hi)
    (generalPlanarLengthWindowCounts_measurable H lo hi)).compl

lemma primitivePlanarWindowBad_subset_nonplanar {g n d : ℕ} (lo hi : Fin d→ℝ≥0)
    (hscale : pantsLengthScale g n=Real.sqrt (pantsScale g n)) :
    primitivePlanarWindowBad H (g:=g) (n:=n) lo hi⊆
      {X |∃γ : H.Primitive g n X,H.length γ≤(1+∑j,(hi j:ℝ))/Real.sqrt (pantsScale g n) ∧H.planarSide γ=none} := by
  intro X hX
  by_contra hno
  apply hX
  funext j
  apply primitive_planar_Ioc_window_count_eq H X (lo j) (hi j)
  intro γ hγ hnop
  apply hno
  have hcap : (hi j:ℝ)≤1+∑i,(hi i:ℝ) := by
    have hs : (hi j:ℝ)≤∑i,(hi i:ℝ) := Finset.single_le_sum
      (fun i (_:i∈Finset.univ)=>show 0≤(hi i:ℝ) from (hi i).property) (Finset.mem_univ j)
    linarith
  rw [hscale] at hγ
  exact ⟨γ,hγ.trans (div_le_div_of_nonneg_right hcap (Real.sqrt_nonneg _)),hnop⟩

include C MI in
lemma primitivePlanarWindowBad_tendsto_zero {d : ℕ}
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) (lo hi : Fin d→ℝ≥0) :
    Tendsto (fun g=>(wpProbability G g (n g)).real
      (primitivePlanarWindowBad H (g:=g) (n:=n g) lo hi)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _=>ENNReal.toReal_nonneg)) ?_
    (primitiveNonplanar_probability_tendsto_zero T C MI n hn (1+∑j,(hi j:ℝ)) (by positivity))
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hn] with g hg
  letI := wpProbability_isFinite G g (n g)
  exact measureReal_mono (primitivePlanarWindowBad_subset_nonplanar H lo hi hg)

include C MI in
theorem primitive_Ioc_window_counts_poisson {d : ℕ}
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ≥0) (hab : ∀j,lo j≤hi j)
    (hdis : DisjointWindows ℝ≥0 (fun j=>lengthIocWindow (lo j) (hi j)))
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector ℝ≥0 (fun j=>lengthIocWindow (lo j) (hi j)) (primitiveLengthPointProcess H X))
      (productPoissonMeasure (windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l)
        (fun j=>lengthIocWindow (lo j) (hi j)))) id := by
  refine lawConverges_of_eq_off_bad_events (fun g=>wpProbability G g (n g))
    (fun g=>primitiveLengthWindowCounts H (g:=g) (n:=n g) lo hi)
    (fun g=>generalPlanarLengthWindowCounts H (g:=g) (n:=n g) lo hi) _ id ?_ ?_ ?_
    (fun g=>primitivePlanarWindowBad H (g:=g) (n:=n g) lo hi) ?_ ?_ ?_ ?_
  · exact WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)
  · exact Eventually.of_forall (fun g=>(primitiveLengthWindowCounts_measurable H lo hi).aemeasurable)
  · exact Eventually.of_forall (fun g=>(generalPlanarLengthWindowCounts_measurable H lo hi).aemeasurable)
  · exact Eventually.of_forall (fun g=>primitivePlanarWindowBad_measurable H lo hi)
  · exact Eventually.of_forall (fun g X hX=>not_not.mp hX)
  · exact primitivePlanarWindowBad_tendsto_zero H T C MI n hn lo hi
  · exact generalPlanar_length_Ioc_window_count_laws H T C MI n hn lo hi hab hdis l hl

end WP.RandomGeometry
