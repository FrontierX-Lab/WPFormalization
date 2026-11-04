import WPFormalization.RandomGeometry.GeneralPlanarDensitySeries
import WPFormalization.RandomGeometry.GeneralPlanarDensityIntensity
import WPFormalization.Probability.MarkedFirstPointDefinitions

/-! The paper's first systolic length/type distribution, written as a genuine
measure. Its time intensity is 2t dt and its type masses are the actual w_k. -/
noncomputable section
set_option maxHeartbeats 0
namespace WP.RandomGeometry
open WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma quadraticLengthIntensity_univ : quadraticLengthIntensity univ=∞ := by
  rw [quadraticLengthIntensity,Measure.map_apply quadraticLengthIntensity_map_measurable MeasurableSet.univ]
  simp only [preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ici]

lemma generalPlanarDensityTypeMeasure_univ_toReal (P : PsiTheory) (l : ℝ≥0∞) :
    (generalPlanarDensityTypeMeasure P l univ).toReal=generalPlanarTotalWeight P (planarDensitySaddle l) := by
  rw [general_planar_density_type_measure_univ]
  exact ENNReal.toReal_ofReal (general_planar_total_weight_nonneg P _ (planar_density_saddle_mem l).1)

lemma generalPlanarDensityTypeMeasure_univ_ne_zero (P : PsiTheory) (l : ℝ≥0∞) :
    generalPlanarDensityTypeMeasure P l univ≠0 := by
  intro h
  have hpos := general_planar_total_weight_one_le P _ (planar_density_saddle_mem l)
  have hh := generalPlanarDensityTypeMeasure_univ_toReal P l
  rw [h,ENNReal.toReal_zero] at hh
  linarith

lemma generalPlanarFirstArrivalMeasure_density (P : PsiTheory) (l : ℝ≥0∞) :
    markedFirstArrivalMeasure quadraticLengthIntensity (generalPlanarDensityTypeMeasure P l)=
      (quadraticLengthIntensity.withDensity (fun t=>ENNReal.ofReal
        (Real.exp (-generalPlanarTotalWeight P (planarDensitySaddle l)*(t:ℝ)^2)))).prod
        (generalPlanarDensityTypeMeasure P l) := by
  unfold markedFirstArrivalMeasure
  congr 2
  funext t
  rw [generalPlanarDensityTypeMeasure_univ_toReal,quadraticLengthIntensity_Iic,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  congr 2
  ring

def generalPlanarSystolicJointMeasure (P : PsiTheory) (l : ℝ≥0∞) : Measure MarkedFirstState :=
  markedFirstArrivalStateMeasure quadraticLengthIntensity (generalPlanarDensityTypeMeasure P l)

lemma generalPlanarFirstArrivalMeasure_rectangle (P : PsiTheory) (l : ℝ≥0∞)
    (B : Set ℝ≥0) (hB : MeasurableSet B) (k : ℕ) :
    markedFirstArrivalMeasure quadraticLengthIntensity (generalPlanarDensityTypeMeasure P l) (B×ˢ{k})=
      (∫⁻t in B,ENNReal.ofReal (Real.exp (-generalPlanarTotalWeight P (planarDensitySaddle l)*(t:ℝ)^2)) ∂quadraticLengthIntensity)*
        ENNReal.ofReal (generalPlanarDensityTypeWeight P l k) := by
  rw [generalPlanarFirstArrivalMeasure_density,Measure.prod_prod,
    general_planar_density_type_measure_singleton,withDensity_apply _ hB]

lemma generalPlanarSystolicJointMeasure_rectangle (P : PsiTheory) (l : ℝ≥0∞)
    (a b : ℝ≥0) (k : ℕ) :
    generalPlanarSystolicJointMeasure P l (Ioc (a:ℝ≥0∞) (b:ℝ≥0∞)×ˢ{k})=
      (∫⁻t in Ioc a b,ENNReal.ofReal (Real.exp (-generalPlanarTotalWeight P (planarDensitySaddle l)*(t:ℝ)^2)) ∂quadraticLengthIntensity)*
        ENNReal.ofReal (generalPlanarDensityTypeWeight P l k) := by
  rw [generalPlanarSystolicJointMeasure,markedFirstArrivalStateMeasure,
    Measure.map_apply markedFirstEmbed_measurable (measurableSet_Ioc.prod (measurableSet_singleton k))]
  have he : markedFirstEmbed ⁻¹' (Ioc (a:ℝ≥0∞) (b:ℝ≥0∞)×ˢ{k})=Ioc a b×ˢ{k} := by
    ext p
    simp [markedFirstEmbed]
  rw [he,generalPlanarFirstArrivalMeasure_rectangle P l _ measurableSet_Ioc]

lemma generalPlanarSystolicJointMeasure_top (P : PsiTheory) (l : ℝ≥0∞) :
    generalPlanarSystolicJointMeasure P l ({∞}×ˢ(univ : Set ℕ))=0 := by
  rw [generalPlanarSystolicJointMeasure,markedFirstArrivalStateMeasure,
    Measure.map_apply markedFirstEmbed_measurable ((measurableSet_singleton ∞).prod MeasurableSet.univ)]
  have he : markedFirstEmbed ⁻¹' ({∞}×ˢ(univ : Set ℕ))=∅ := by
    ext p
    simp [markedFirstEmbed]
  rw [he,measure_empty]

end WP.RandomGeometry
