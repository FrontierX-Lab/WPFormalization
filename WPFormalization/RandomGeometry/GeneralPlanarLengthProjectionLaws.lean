import WPFormalization.RandomGeometry.GeneralPlanarLengthTruncatedLaws
import WPFormalization.RandomGeometry.GeneralPlanarOriginalTypeTail
import WPFormalization.Probability.PoissonTruncation

/-! The actual length projection is obtained by finite type truncation and
uniform control of actual large planar cusp sides. No improper projection of
the marked vague topology is used. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def generalPlanarLengthWindowCounts {g n d : ℕ} (lo hi : Fin d→ℝ≥0)
    (X : G.Moduli g n (fun _=>0)) : Fin d→ℕ :=
  windowCountVector ℝ≥0 (fun j=>lengthIocWindow (lo j) (hi j)) (generalPlanarLengthPointProcess H X)

def generalPlanarLengthProjectionBad (g n K : ℕ) (t : ℝ) : Set (G.Moduli g n (fun _=>0)) :=
  {X |∃γ : H.Primitive g n X,H.length γ≤t/Real.sqrt (pantsScale g n) ∧
    ∃S : Finset (Fin n),H.planarSide γ=some S ∧K+2≤S.card}

lemma generalPlanarLengthProjectionBad_measurable (g n K : ℕ) (t : ℝ) :
    MeasurableSet (generalPlanarLengthProjectionBad H g n K t) := by
  have he : generalPlanarLengthProjectionBad H g n K t=
      {X |0<generalPlanarTypeTailCount H X K (t/Real.sqrt (pantsScale g n))} := by
    ext X
    exact (generalPlanar_type_tail_pos_iff H X K _).symm
  rw [he]
  exact measurableSet_lt measurable_const (generalPlanar_type_tail_measurable H K _)

lemma generalPlanarLengthWindowCounts_measurable {g n d : ℕ} (lo hi : Fin d→ℝ≥0) :
    Measurable (generalPlanarLengthWindowCounts H (g:=g) (n:=n) lo hi) := by
  apply Measurable.of_eval
  intro j
  exact generalPlanarLengthPointProcess_Ioc_count_measurable H (lo j) (hi j)

lemma generalPlanarLengthWindowCounts_eq_truncation_off_bad {g n d : ℕ} (K : ℕ)
    (lo hi : Fin d→ℝ≥0) (hscale : pantsLengthScale g n=Real.sqrt (pantsScale g n))
    (X : G.Moduli g n (fun _=>0))
    (hX : X∉generalPlanarLengthProjectionBad H g n K (1+∑j,(hi j:ℝ))) :
    generalPlanarLengthWindowCounts H lo hi X=generalPlanarLengthTruncatedCounts H K lo hi X := by
  funext j
  apply generalPlanarLengthPointProcess_window_partition H X (lengthIocWindow (lo j) (hi j)) (K+2)
  intro γ hp hγ
  by_contra hlarge
  have hm : K+2≤planarPrimitiveCuspType H γ := by omega
  obtain ⟨S,hS⟩ := hp
  have hmem := (scaled_length_mem_Ioc (pantsLengthScale g n) (pantsLengthScale_pos g n)
    (lo j) (hi j) (H.length γ)).mp hγ
  have hcap : (hi j:ℝ)≤1+∑i,(hi i:ℝ) := by
    have hs : (hi j:ℝ)≤∑i,(hi i:ℝ) := Finset.single_le_sum
      (fun i (_:i∈Finset.univ)=>show 0≤(hi i:ℝ) from (hi i).property) (Finset.mem_univ j)
    linarith
  apply hX
  refine ⟨γ,?_,S,hS,?_⟩
  · rw [hscale] at hmem
    exact hmem.2.trans (div_le_div_of_nonneg_right hcap (Real.sqrt_nonneg _))
  · rwa [planarPrimitiveCuspType_of_side H γ S hS] at hm

include C MI in
theorem generalPlanar_length_Ioc_counts_poisson {d : ℕ}
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ≥0) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarLengthWindowCounts H (g:=g) (n:=n g) lo hi)
      (productPoissonMeasure (fun j=>generalPlanarDensityLengthRate P l
        (Real.toNNReal ((hi j:ℝ)^2-(lo j:ℝ)^2)))) id := by
  refine lawConverges_poisson_of_truncations (fun g=>wpProbability G g (n g))
    (fun g=>generalPlanarLengthWindowCounts H (g:=g) (n:=n g) lo hi)
    (fun K g=>generalPlanarLengthTruncatedCounts H (g:=g) (n:=n g) K lo hi)
    (fun K j=>generalPlanarDensityLengthTruncatedRate P l K (Real.toNNReal ((hi j:ℝ)^2-(lo j:ℝ)^2))) _ ?_ ?_ ?_
    (fun K g=>generalPlanarLengthProjectionBad H g (n g) K (1+∑j,(hi j:ℝ))) ?_ ?_ ?_ ?_ ?_
  · exact WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)
  · exact Eventually.of_forall (fun g=>(generalPlanarLengthWindowCounts_measurable H lo hi).aemeasurable)
  · intro K
    exact Eventually.of_forall (fun g=>(generalPlanarLengthTruncatedCounts_measurable H K lo hi).aemeasurable)
  · intro K
    exact Eventually.of_forall (fun g=>generalPlanarLengthProjectionBad_measurable H g (n g) K _)
  · intro K
    filter_upwards [pantsLengthScale_eventually_eq_sqrt n hn] with g hg
    exact generalPlanarLengthWindowCounts_eq_truncation_off_bad H K lo hi hg
  · intro ε hε
    have ht : 0≤1+∑j,(hi j:ℝ) := by positivity
    obtain ⟨K0,hK0⟩ := generalPlanar_original_large_side_probability_uniform H T C MI n hn _ ht ε hε
    exact ⟨K0,fun K hK=>hK0.mono (fun g hg=>hg K hK)⟩
  · intro K
    exact generalPlanar_length_truncated_counts_poisson H T C MI K n hn lo hi hab hdis l hl
  · intro j
    exact general_planar_density_length_truncated_rate_tendsto P l _

end WP.RandomGeometry
