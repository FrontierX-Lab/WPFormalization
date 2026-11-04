import WPFormalization.RandomGeometry.PrimitiveSystolicFirstPoint
import WPFormalization.RandomGeometry.GeneralPlanarFirstPointIntensity
import WPFormalization.Probability.MarkedFirstPointMarginals
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The discrete marginal of the genuine joint first-point law. The joint-law
hypothesis is an internal transfer interface, eliminated by the final theorem. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical

lemma generalPlanarSystolicJointMeasure_mark_real (P : PsiTheory) (l : ℝ≥0∞)
    [IsProbabilityMeasure (generalPlanarSystolicJointMeasure P l)] (k : ℕ) :
    (generalPlanarSystolicJointMeasure P l).real {p|p.2=k}=
      generalPlanarDensityTypeWeight P l k/generalPlanarTotalWeight P (planarDensitySaddle l) := by
  letI : IsProbabilityMeasure (markedFirstArrivalStateMeasure quadraticLengthIntensity (generalPlanarDensityTypeMeasure P l)) :=
    ‹IsProbabilityMeasure (generalPlanarSystolicJointMeasure P l)›
  change (markedFirstArrivalStateMeasure quadraticLengthIntensity (generalPlanarDensityTypeMeasure P l)).real _=_
  rw [markedFirstArrivalStateMeasure_mark_real]
  simp only [Measure.real,general_planar_density_type_measure_singleton,
    ENNReal.toReal_ofReal (general_planar_density_type_weight_nonneg P l k),generalPlanarDensityTypeMeasure_univ_toReal]

def primitiveSystolicMarkTest (k : ℕ) : BoundedContinuousFunction MarkedFirstState ℝ :=
  (BoundedContinuousFunction.mkOfDiscrete (fun j : ℕ=>if j=k then (1:ℝ) else 0) 1 (by
    intro a b
    split_ifs <;>norm_num)).compContinuous ⟨Prod.snd,continuous_snd⟩

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G)

lemma primitiveSystolicSelectedState_mark_probability_of_joint_law (n : ℕ→ℕ)
    (l : ℝ≥0∞) [IsProbabilityMeasure (generalPlanarSystolicJointMeasure P l)]
    (k : ∀g,G.Moduli g (n g) (fun _=>0)→ℕ) (hk : ∀ᶠg in atTop,Measurable (k g))
    (hlaw : LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>primitiveSystolicSelectedState H X (k g X)) (generalPlanarSystolicJointMeasure P l) id)
    (j : ℕ) :
    Tendsto (fun g=>(wpProbability G g (n g)).real {X|k g X=j}) atTop
      (𝓝 (generalPlanarDensityTypeWeight P l j/generalPlanarTotalWeight P (planarDensitySaddle l))) := by
  have hh := hlaw (primitiveSystolicMarkTest j)
  have hi : (∫p,primitiveSystolicMarkTest j p ∂generalPlanarSystolicJointMeasure P l)=
      generalPlanarDensityTypeWeight P l j/generalPlanarTotalWeight P (planarDensitySaddle l) := by
    have he : (fun p : MarkedFirstState=>primitiveSystolicMarkTest j p)=
        ({p : MarkedFirstState|p.2=j}:Set MarkedFirstState).indicator (fun _=>(1:ℝ)) := by
      funext p
      simp [primitiveSystolicMarkTest,indicator]
    rw [he]
    calc
      _ = (generalPlanarSystolicJointMeasure P l).real {p|p.2=j} :=
        integral_indicator_one ((measurableSet_singleton j).preimage measurable_snd)
      _ = _ := generalPlanarSystolicJointMeasure_mark_real P l j
  simp only [id_eq,hi] at hh
  apply hh.congr'
  filter_upwards [hk] with g hg
  have he : (fun X : G.Moduli g (n g) (fun _=>0)=>primitiveSystolicMarkTest j (primitiveSystolicSelectedState H X (k g X)))=
      ({X : G.Moduli g (n g) (fun _=>0)|k g X=j}:Set _).indicator (fun _=>(1:ℝ)) := by
    funext X
    simp [primitiveSystolicMarkTest,primitiveSystolicSelectedState,indicator]
  rw [he]
  exact integral_indicator_one ((measurableSet_singleton j).preimage hg)

end WP.RandomGeometry
