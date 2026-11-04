import WPFormalization.RandomGeometry.PrimitiveSystolicPlanarity

/-! The literal probability-one statement for every systolic primitive,
including every choice in a length tie. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma primitive_all_systolic_planar_iff_no_nonplanar {g n : ℕ} (X : G.Moduli g n (fun _=>0)) :
    (∀γ : H.Primitive g n X,IsSystolicPrimitive H γ→IsPlanarPrimitive H γ)↔
      ¬∃γ : H.Primitive g n X,IsSystolicPrimitive H γ ∧H.planarSide γ=none := by
  constructor
  · rintro hh ⟨γ,hγ,hno⟩
    obtain ⟨S,hS⟩ := hh γ hγ
    rw [hno] at hS
    cases hS
  · intro hh γ hγ
    cases hs : H.planarSide γ with
    | none => exact (hh ⟨γ,hγ,hs⟩).elim
    | some S => exact ⟨S,hs⟩

include C MI in
theorem primitive_all_systolic_planar_probability_tendsto_one (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) :
    Tendsto (fun g=>(wpProbability G g (n g)).real
      {X |∀γ : H.Primitive g (n g) X,IsSystolicPrimitive H γ→IsPlanarPrimitive H γ}) atTop (𝓝 1) := by
  have hbad := primitive_systolic_nonplanar_probability_tendsto_zero H T C MI n hn
  have hone : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlo := hone.sub hbad
  simp only [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)] with g hg
    letI := hg
    let A := {X : G.Moduli g (n g) (fun _=>0)|
      ∀γ : H.Primitive g (n g) X,IsSystolicPrimitive H γ→IsPlanarPrimitive H γ}
    let B := {X : G.Moduli g (n g) (fun _=>0)|
      ∃γ : H.Primitive g (n g) X,IsSystolicPrimitive H γ ∧H.planarSide γ=none}
    have hu : A∪B=univ := by
      ext X
      simp only [mem_union,mem_univ,iff_true]
      by_cases hx : X∈B
      · exact Or.inr hx
      · exact Or.inl ((primitive_all_systolic_planar_iff_no_nonplanar H X).mpr hx)
    have hh := measureReal_union_le (μ:=wpProbability G g (n g)) A B
    rw [hu] at hh
    simp only [Measure.real,measure_univ,ENNReal.toReal_one] at hh
    change 1-(wpProbability G g (n g)).real B≤(wpProbability G g (n g)).real A
    change 1≤(wpProbability G g (n g)).real A+(wpProbability G g (n g)).real B at hh
    linarith
  · filter_upwards [WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)] with g hg
    letI := hg
    exact measureReal_le_one

end WP.RandomGeometry
