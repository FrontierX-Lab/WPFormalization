import WPFormalization.RandomGeometry.GeneralPlanarMarkedPointProcess
import WPFormalization.RandomGeometry.GeneralPlanarOriginalTypeTail

/-! The actual marked family is finite over every bounded length prefix,
including all integer marks. Its no-escape estimate is the actual type tail. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma generalPlanarMarkedLengthPointProcess_prefix_all_types_lt_top
    (X : G.Moduli g n (fun _=>0)) (t : ℝ≥0) :
    (generalPlanarMarkedLengthPointProcess H X).toMeasure (Iic t×ˢ(univ : Set ℕ))<∞ := by
  let B := Iic t×ˢ(univ : Set ℕ)
  have hb : BddAbove (Prod.fst '' B) := by
    refine ⟨t,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact hx.1
  letI := genericMarkedCurveLengthMeasure_finite_window H X _ (pantsLengthScale_pos g n)
    (IsPlanarPrimitive H) (planarPrimitiveCuspType H) B hb
  change genericMarkedCurveLengthMeasure H X _ _ _ B<∞
  rw [genericMarkedCurveLengthMeasure,sum_dirac_apply_eq_natCard _ _ (measurableSet_Iic.prod MeasurableSet.univ)]
  exact ENNReal.natCast_lt_top _

lemma generalPlanarMarkedLengthPointProcess_tail_nonzero_iff
    (X : G.Moduli g n (fun _=>0)) (t : ℝ≥0) (K : ℕ) :
    (generalPlanarMarkedLengthPointProcess H X).toMeasure (Iic t×ˢIci K)≠0 ↔
      ∃γ : H.Primitive g n X,H.length γ≤(t:ℝ)/pantsLengthScale g n ∧
        ∃S : Finset (Fin n),H.planarSide γ=some S ∧K≤S.card := by
  let B := Iic t×ˢIci K
  have hb : BddAbove (Prod.fst '' B) := by
    refine ⟨t,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact hx.1
  let A := {γ : {γ : H.Primitive g n X //IsPlanarPrimitive H γ} //
    (Real.toNNReal (pantsLengthScale g n*H.length γ.val),planarPrimitiveCuspType H γ.val)∈B}
  letI : Finite A := genericMarkedCurveLengthMeasure_finite_window H X _ (pantsLengthScale_pos g n)
    (IsPlanarPrimitive H) (planarPrimitiveCuspType H) B hb
  change genericMarkedCurveLengthMeasure H X _ _ _ B≠0 ↔_
  rw [genericMarkedCurveLengthMeasure,sum_dirac_apply_eq_natCard _ _ (measurableSet_Iic.prod measurableSet_Ici)]
  have hcard : (Nat.card A:ℝ≥0∞)≠0 ↔Nonempty A := by
    letI : Fintype A := Fintype.ofFinite A
    simp only [Nat.card_eq_fintype_card,ne_eq,Nat.cast_eq_zero]
    exact Nat.pos_iff_ne_zero.symm.trans Fintype.card_pos_iff
  rw [hcard]
  constructor
  · rintro ⟨⟨⟨γ,S,hS⟩,hγ⟩⟩
    refine ⟨γ,?_,S,hS,?_⟩
    · have hh := (Real.toNNReal_le_iff_le_coe).mp hγ.1
      exact (le_div_iff₀ (pantsLengthScale_pos g n)).mpr (by simpa only [mul_comm] using hh)
    · simpa only [mem_Ici,planarPrimitiveCuspType_of_side H γ S hS] using hγ.2
  · rintro ⟨γ,hγ,S,hS,hK⟩
    refine ⟨⟨⟨γ,⟨S,hS⟩⟩,?_,?_⟩⟩
    · exact Real.toNNReal_le_iff_le_coe.mpr (by
        have hh := (le_div_iff₀ (pantsLengthScale_pos g n)).mp hγ
        simpa only [mul_comm] using hh)
    · simpa only [mem_Ici,planarPrimitiveCuspType_of_side H γ S hS] using hK

variable (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
theorem generalPlanarMarkedLengthPointProcess_no_escape
    (n : ℕ→ℕ) (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (t : ℝ≥0) :
    ∀ε : ℝ,0<ε→∃K₀ : ℕ,∀ᶠg : ℕ in atTop,∀K : ℕ,K₀≤K→
      (wpProbability G g (n g)) {X |
        (generalPlanarMarkedLengthPointProcess H X).toMeasure (Iic t×ˢIci K)≠0}≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨K₀,hK₀⟩ := generalPlanar_original_large_side_probability_uniform H T C MI n hn (t:ℝ) t.property ε hε
  refine ⟨K₀+2,?_⟩
  filter_upwards [hK₀,pantsLengthScale_eventually_eq_sqrt n hn] with g hg hs
  intro K hK
  letI := wpProbability_isFinite G g (n g)
  have hsub : {X : G.Moduli g (n g) (fun _=>0)|
      (generalPlanarMarkedLengthPointProcess H X).toMeasure (Iic t×ˢIci K)≠0}⊆
      {X |∃γ : H.Primitive g (n g) X,H.length γ≤(t:ℝ)/Real.sqrt (pantsScale g (n g)) ∧
        ∃S : Finset (Fin (n g)),H.planarSide γ=some S ∧K₀+2≤S.card} := by
    intro X hX
    obtain ⟨γ,hγ,S,hS,hcard⟩ := (generalPlanarMarkedLengthPointProcess_tail_nonzero_iff H X t K).mp hX
    exact ⟨γ,by simpa only [hs] using hγ,S,hS,hK.trans hcard⟩
  have hbound := (measure_mono hsub).trans (show
    (wpProbability G g (n g)) {X |∃γ : H.Primitive g (n g) X,
      H.length γ≤(t:ℝ)/Real.sqrt (pantsScale g (n g)) ∧
        ∃S : Finset (Fin (n g)),H.planarSide γ=some S ∧K₀+2≤S.card}≤ENNReal.ofReal ε from by
    rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hg K₀ le_rfl))
  exact hbound

end WP.RandomGeometry
