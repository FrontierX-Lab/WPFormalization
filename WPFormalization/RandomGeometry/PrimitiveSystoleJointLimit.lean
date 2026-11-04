import WPFormalization.RandomGeometry.PrimitiveSystolicMarkProbability
import WPFormalization.RandomGeometry.PrimitiveSystolicPlanarityProbability
import WPFormalization.RandomGeometry.GeneralPlanarMarkedPoissonProcess
import WPFormalization.Probability.MarkedFirstPoint

/-! The actual joint systolic length/cusp-type limit in (14.5). The tie rule
can choose any shortest actual primitive, subject only to measurability. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (D : MarkedPoissonFirstPointData) (FC : MarkedFirstPointConvergence.{v})

include C MI D in
lemma generalPlanarSystolicJointMeasure_probability (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    IsProbabilityMeasure (generalPlanarSystolicJointMeasure P l) := by
  obtain ⟨Q,hQ,hL⟩ := generalPlanar_marked_poisson_process H T C MI n hn l hl
  exact markedFirstArrivalStateMeasure_isProbabilityMeasure D quadraticLengthIntensity
    (generalPlanarDensityTypeMeasure P l) quadraticLengthIntensity_univ
    (generalPlanarDensityTypeMeasure_univ_ne_zero P l) Q hQ

include C MI D FC in
theorem primitive_systole_joint_type_limit (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l))
    (k : ∀g,G.Moduli g (n g) (fun _=>0)→ℕ)
    (hkmeas : ∀ᶠg in atTop,Measurable (k g))
    (hkspec : ∀ᶠg in atTop,∀X,IsSystolicTypeSelection H X (k g X)) :
    IsProbabilityMeasure (generalPlanarSystolicJointMeasure P l) ∧
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>(ENNReal.ofReal (Real.sqrt (pantsScale g (n g)))*primitiveMinimumLength H X,k g X))
      (generalPlanarSystolicJointMeasure P l) id ∧
    ∀j : ℕ,Tendsto (fun g=>(wpProbability G g (n g)).real {X|k g X=j}) atTop
      (𝓝 (generalPlanarDensityTypeWeight P l j/generalPlanarTotalWeight P (planarDensitySaddle l))) := by
  obtain ⟨Q,hQ,hL⟩ := generalPlanar_marked_poisson_process H T C MI n hn l hl
  have hprob := WP.Spectral.wpProbability_eventually_probability P G n
    ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)
  have hΞ : ∀ᶠg in atTop,AEMeasurable
      (fun X : G.Moduli g (n g) (fun _=>0)=>generalPlanarMarkedLengthPointProcess H X) (wpProbability G g (n g)) :=
    Eventually.of_forall (fun g=>generalPlanarMarkedLengthPointProcess_aemeasurable H l _)
  have hS : ∀ᶠg in atTop,AEMeasurable
      (fun X : G.Moduli g (n g) (fun _=>0)=>primitiveSystolicSelectedState H X (k g X)) (wpProbability G g (n g)) := by
    filter_upwards [hkmeas] with g hg
    exact (primitiveSystolicSelectedState_measurable H (k g) hg).aemeasurable
  have hpref : ∀ᶠg in atTop,∀ᵐX ∂wpProbability G g (n g),
      MarkedTimePrefixFinite (generalPlanarMarkedLengthPointProcess H X) :=
    Eventually.of_forall (fun g=>Eventually.of_forall (generalPlanarMarkedLengthPointProcess_timePrefixFinite H))
  obtain ⟨hJ,hJoint⟩ := lawConverges_marked_first_point D FC quadraticLengthIntensity
    (generalPlanarDensityTypeMeasure P l) quadraticLengthIntensity_univ
    (generalPlanarDensityTypeMeasure_univ_ne_zero P l) Q hQ
    (fun g=>wpProbability G g (n g))
    (fun g X=>generalPlanarMarkedLengthPointProcess H X)
    (fun g X=>primitiveSystolicSelectedState H X (k g X))
    hprob hΞ hS hpref
    (primitiveSystolicSelectedState_invalid_tendsto_zero H T C MI n hn k hkspec)
    (generalPlanarMarkedLengthPointProcess_markedNoEscape H T C MI n hn) hL
  letI : IsProbabilityMeasure (generalPlanarSystolicJointMeasure P l) := hJ
  have hj : LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>primitiveSystolicSelectedState H X (k g X)) (generalPlanarSystolicJointMeasure P l) id := hJoint
  refine ⟨hJ,?_,fun j=>primitiveSystolicSelectedState_mark_probability_of_joint_law H n l k hkmeas hj j⟩
  intro f
  apply (hj f).congr'
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hn] with g hg
  apply integral_congr_ae
  exact Eventually.of_forall (fun X=>by simp only [primitiveSystolicSelectedState,hg])

end WP.RandomGeometry
