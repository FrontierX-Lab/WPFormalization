import WPFormalization.Analysis.ParameterDerivatives

/-! Analyticity of the actual J and density functions. Complex C¹ implicit
branches make their affine integrals analytic in one complex variable;
local uniqueness identifies the original real branch, including at Y=0. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma XR_analyticAt (Y : ℝ) : AnalyticAt ℝ XR Y := by
  have hc : AnalyticAt ℝ (fun x : ℝ => X (x:ℂ)) Y :=
    (X_differentiable.analyticAt (Y:ℂ)).restrictScalars.comp (Complex.ofRealCLM.analyticAt Y)
  exact (Complex.reCLM.analyticAt _).comp hc
lemma J_analyticAt_on_stationaryParameterDomain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    AnalyticAt ℝ WP.J Y := by
  let H (p : ComplexPair) : ℂ := ∫ s : ℝ in (0)..1,X (stationaryQLinear s p)
  have hc : ContDiff ℂ 1 H := by
    simpa only [H,zero_add,one_mul] using
      affineIntegral_prod_contDiff_one (fun _ => 1) (fun _ => 0) stationaryQLinear
        continuous_const continuous_const stationaryQLinear_continuous X X_differentiable
  have hbase := stationaryQ_zero_of_real_zero Y (WP.T Y)
    (T_root_on_stationaryParameterDomain Y hY).2
  have heq : ∀ᶠ x : ℝ in 𝓝 Y,stationaryQProd ((x:ℂ),(WP.T x:ℂ)) = stationaryQProd ((Y:ℂ),(WP.T Y:ℂ)) := by
    filter_upwards [stationaryParameterDomain_isOpen.mem_nhds hY] with x hx
    rw [hbase,stationaryQ_zero_of_real_zero x (WP.T x) (T_root_on_stationaryParameterDomain x hx).2]
  have ha := analyticAt_real_implicit_comp stationaryQProd H WP.T Y
    stationaryQ_contDiff_one.contDiffAt hc.contDiffAt (stationaryQ_partial_isInvertible Y hY)
    (T_continuousAt_on_stationaryParameterDomain Y hY) heq
  have he : (fun x : ℝ => (H ((x:ℂ),(WP.T x:ℂ))).re) = WP.J := by
    funext x
    simpa only [H,stationaryWeighted,Complex.ofReal_one,one_mul] using stationaryWeighted_one_X x
  rwa [he] at ha
lemma J_analyticAt_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : AnalyticAt ℝ WP.J Y :=
  J_analyticAt_on_stationaryParameterDomain Y (stationaryParameterDomain_contains Y hY)
lemma J_action_identity_on_domain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    WP.J Y = XR Y+WP.action Y/Real.sqrt (WP.Delta Y) := by
  have hs := T_root_on_stationaryParameterDomain Y hY
  have ht : Y < WP.T Y := lt_trans hY.1 hs.1.1
  simpa only [WP.J,WP.action,WP.Delta] using WP.J_action_integral Y (WP.T Y) ht
lemma density_J_formula_on_domain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    WP.density Y = 2*XR Y/(WP.J Y-XR Y) := by
  have he : WP.J Y-XR Y = WP.action Y/Real.sqrt (WP.Delta Y) := by
    linarith [J_action_identity_on_domain Y hY]
  rw [he,div_div_eq_mul_div]
  rfl
lemma J_sub_XR_pos_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < WP.J Y-XR Y := by
  rw [WP.J_action_identity Y hY]
  simpa only [add_sub_cancel_left] using div_pos (WP.action_pos Y hY)
    (Real.sqrt_pos.mpr (WP.Delta_pos Y hY))
lemma density_analyticAt_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : AnalyticAt ℝ WP.density Y := by
  have ha : AnalyticAt ℝ (fun x : ℝ => 2*XR x/(WP.J x-XR x)) Y :=
    (analyticAt_const.mul (XR_analyticAt Y)).div
      ((J_analyticAt_interior Y hY).sub (XR_analyticAt Y)) (J_sub_XR_pos_interior Y hY).ne'
  apply ha.congr
  filter_upwards [stationaryParameterDomain_isOpen.mem_nhds (stationaryParameterDomain_contains Y hY)] with x hx
  exact (density_J_formula_on_domain x hx).symm

end WP.Analysis
