import WPFormalization.RandomGeometry.PrimitiveSystolicSelection
import WPFormalization.Probability.MarkedFirstPointDefinitions

/-! A measurable choice of any actual systolic primitive is a first marked
atom outside the already controlled nonplanar-systolic event. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def primitiveSystolicSelectedState (X : G.Moduli g n (fun _=>0)) (k : ℕ) : MarkedFirstState :=
  (ENNReal.ofReal (pantsLengthScale g n)*primitiveMinimumLength H X,k)

lemma primitiveSystolicSelectedState_measurable (k : G.Moduli g n (fun _=>0)→ℕ) (hk : Measurable k) :
    Measurable (fun X=>primitiveSystolicSelectedState H X (k X)) := by
  exact (measurable_const.mul (primitiveMinimumLength_measurable H)).prodMk hk

lemma primitiveSystolicSelectedState_isFirst (X : G.Moduli g n (fun _=>0)) (k : ℕ)
    (hk : IsSystolicTypeSelection H X k)
    (hno : ¬∃γ : H.Primitive g n X,IsSystolicPrimitive H γ ∧H.planarSide γ=none) :
    IsFirstMarkedPoint (generalPlanarMarkedLengthPointProcess H X) (primitiveSystolicSelectedState H X k) := by
  rcases hk with ⟨γ,hγ,rfl⟩|⟨he,rfl⟩
  · have hp : IsPlanarPrimitive H γ := by
      cases hs : H.planarSide γ with
      | none => exact (hno ⟨γ,hγ,hs⟩).elim
      | some S => exact ⟨S,hs⟩
    change IsFirstMarkedPoint _ (ENNReal.ofReal (pantsLengthScale g n)*primitiveMinimumLength H X,_)
    rw [primitive_systolic_scaled_length_eq H X γ hγ]
    simp only [IsFirstMarkedPoint,ENNReal.ofReal_ne_top,ite_false,ENNReal.ofReal,ENNReal.toNNReal_coe]
    exact ⟨generalPlanarMarkedLengthPointProcess_atom_of_planar H X γ hp,
      generalPlanarMarkedLengthPointProcess_before_systolic_eq_zero H X γ hγ⟩
  · change IsFirstMarkedPoint _ (ENNReal.ofReal (pantsLengthScale g n)*primitiveMinimumLength H X,0)
    rw [primitiveMinimumLength_eq_top_of_isEmpty H X he]
    have hs : ENNReal.ofReal (pantsLengthScale g n)≠0 := ENNReal.ofReal_ne_zero_iff.mpr (pantsLengthScale_pos g n)
    rw [ENNReal.mul_top hs,isFirstMarkedPoint_top]
    exact generalPlanarMarkedLengthPointProcess_eq_zero_of_isEmpty H X he

lemma primitiveSystolicSelectedState_invalid_subset (k : G.Moduli g n (fun _=>0)→ℕ)
    (hk : ∀X,IsSystolicTypeSelection H X (k X)) :
    {X |¬IsFirstMarkedPoint (generalPlanarMarkedLengthPointProcess H X) (primitiveSystolicSelectedState H X (k X))}⊆
      {X |∃γ : H.Primitive g n X,IsSystolicPrimitive H γ ∧H.planarSide γ=none} := by
  intro X hX
  by_contra hn
  exact hX (primitiveSystolicSelectedState_isFirst H X (k X) (hk X) hn)

lemma generalPlanarMarkedLengthPointProcess_timePrefixFinite (X : G.Moduli g n (fun _=>0)) :
    MarkedTimePrefixFinite (generalPlanarMarkedLengthPointProcess H X) :=
  generalPlanarMarkedLengthPointProcess_prefix_all_types_lt_top H X

variable (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (MI : MirzakhaniIntegration G H T)

include C MI in
lemma generalPlanarMarkedLengthPointProcess_markedNoEscape (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) :
    MarkedNoEscape (fun g=>wpProbability G g (n g)) (fun g X=>generalPlanarMarkedLengthPointProcess H X) := by
  intro t ε hε
  obtain ⟨K,hK⟩ := generalPlanarMarkedLengthPointProcess_no_escape H T C MI n hn t ε hε
  exact ⟨K,hK.mono (fun g hg=>hg K le_rfl)⟩

include C MI in
theorem primitiveSystolicSelectedState_invalid_tendsto_zero (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (k : ∀g,G.Moduli g (n g) (fun _=>0)→ℕ)
    (hk : ∀ᶠg in atTop,∀X,IsSystolicTypeSelection H X (k g X)) :
    Tendsto (fun g=>(wpProbability G g (n g)) {X |
      ¬IsFirstMarkedPoint (generalPlanarMarkedLengthPointProcess H X) (primitiveSystolicSelectedState H X (k g X))}) atTop (𝓝 0) := by
  have hl := ENNReal.tendsto_ofReal (primitive_systolic_nonplanar_probability_tendsto_zero H T C MI n hn)
  simp only [ENNReal.ofReal_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl (Eventually.of_forall (fun _=>bot_le))
  filter_upwards [hk] with g hg
  letI := wpProbability_isFinite G g (n g)
  simp only [Measure.real]
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact measure_mono (primitiveSystolicSelectedState_invalid_subset H (k g) hg)

end WP.RandomGeometry
