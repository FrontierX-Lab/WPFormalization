import WPFormalization.HigherOrder.Endpoint
import WPFormalization.HigherOrder.FirstCorrectionPrimitive
/-! The original integral-defined logarithmic marked coefficients have true real continuity, derivatives and endpoint variation from a removable quotient. The totalized raw endpoint value is not identified with its continuation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.HigherOrder
lemma logarithmicMarkedCoefficient_regular_of_quotient (P:PsiTheory)(p j:ℕ)(hj:1 ≤ j) (q : ℝ→ℝ)
    (hq : ContinuousOn q (Icc (0:ℝ) y₀))
    (heq : ∀ Y∈Ico (0:ℝ) y₀,q Y=transportCoefficient P p j Y/(A Y*r Y)) :
    ContinuousOn (logarithmicMarkedCoefficient P p j) (Icc (0:ℝ) y₀) ∧
    (∀ Y∈Ioo (0:ℝ) y₀,HasDerivAt (logarithmicMarkedCoefficient P p j)
      (transportCoefficient P p j Y/(A Y*r Y)) Y) := by
  let qc (x : ℝ) : ℝ := q (max 0 (min x y₀))
  have hclamp (x : ℝ) : max 0 (min x y₀)∈Icc (0:ℝ) y₀ :=
    ⟨le_max_left _ _,max_le y₀_pos.le (min_le_right _ _)⟩
  have hqcOn : ContinuousOn qc univ := hq.comp
    ((continuous_const.max (continuous_id.min continuous_const)).continuousOn)
    (fun x _ => hclamp x)
  have hqc : Continuous qc := continuousOn_univ.mp hqcOn
  have hagree (x : ℝ) (hx : x∈Icc (0:ℝ) y₀) : qc x=q x := by
    dsimp [qc]
    rw [min_eq_left hx.2,max_eq_right hx.1]
  have hLeq (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
      logarithmicMarkedCoefficient P p j Y=endpointLogCoefficient p j-∫ x in Y..y₀,qc x := by
    simp only[logarithmicMarkedCoefficient,ite_eq_right (show j≠0 by omega)]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le hY.2
    intro x hx
    have hxi : x∈Ico (0:ℝ) y₀ := ⟨hY.1.trans hx.1.le,hx.2⟩
    exact (heq x hxi).symm.trans (hagree x ⟨hxi.1,hxi.2.le⟩).symm
  have hint : IntegrableOn qc (uIcc (0:ℝ) y₀) := by
    rw [uIcc_of_le y₀_pos.le]
    exact hqc.continuousOn.integrableOn_Icc
  have hprim := intervalIntegral.continuousOn_primitive_interval_left hint
  rw [uIcc_of_le y₀_pos.le] at hprim
  have hLcont : ContinuousOn (logarithmicMarkedCoefficient P p j) (Icc (0:ℝ) y₀) :=
    (continuousOn_const.sub hprim).congr hLeq
  refine ⟨hLcont,?_⟩
  · intro Y hY
    have hI := intervalIntegral.integral_hasDerivAt_left (hqc.intervalIntegrable Y y₀)
      (hqc.stronglyMeasurableAtFilter volume (𝓝 Y)) hqc.continuousAt
    have hd : HasDerivAt (fun x => endpointLogCoefficient p j-∫ v in x..y₀,qc v) (qc Y) Y := by
      convert (hasDerivAt_const Y (endpointLogCoefficient p j)).sub hI using 1 <;> ring
    have hE : logarithmicMarkedCoefficient P p j =ᶠ[𝓝 Y] (fun x => endpointLogCoefficient p j-∫ v in x..y₀,qc v) := by
      filter_upwards [isOpen_Ioo.mem_nhds hY] with x hx
      exact hLeq x ⟨hx.1.le,hx.2.le⟩
    have hval : qc Y=transportCoefficient P p j Y/(A Y*r Y) :=
      (hagree Y ⟨hY.1.le,hY.2.le⟩).trans (heq Y ⟨hY.1.le,hY.2⟩)
    rw [hval] at hd
    exact hd.congr_of_eventuallyEq hE

lemma logarithmicMarkedCoefficient_endpoint_lipschitz_of_quotient (P:PsiTheory)(p j:ℕ)(hj:1 ≤ j)
    (q:ℝ→ℝ)(heq:∀Y∈Ico (0:ℝ) y₀,q Y=transportCoefficient P p j Y/(A Y*r Y))
    (M:ℝ)(hM:0 ≤ M)(hq:∀Y∈Icc (0:ℝ) y₀,|q Y| ≤ M)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    |logarithmicMarkedCoefficient P p j Y-endpointLogCoefficient p j| ≤ M*(y₀-Y) := by
  have hIEq:(∫x in Y..y₀,transportCoefficient P p j x/(A x*r x))=∫x in Y..y₀,q x:=by
    apply intervalIntegral.integral_congr_Ioo_of_le hY.2
    intro x hx
    exact (heq x ⟨hY.1.trans hx.1.le,hx.2⟩).symm
  have hb:‖∫x in Y..y₀,q x‖ ≤ M*|y₀-Y|:=intervalIntegral.norm_integral_le_of_norm_le_const (by
    intro x hx
    rw[uIoc_of_le hY.2] at hx
    simpa only[Real.norm_eq_abs] using hq x ⟨hY.1.trans hx.1.le,hx.2⟩)
  simp only[logarithmicMarkedCoefficient,ite_eq_right (show j≠0 by omega)]
  rw[sub_sub_cancel_left,abs_neg,hIEq]
  simpa only[Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hY.2)] using hb
end WP.HigherOrder
