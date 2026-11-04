import WPFormalization.Analysis.CriticalParameterCoordinates

/-! Complete critical asymptotics for the original action, density and
profile functions. Local analytic factors give the relative error; the
actual density inverse and compact integral identities give the profiles
and the two-sided beta scale comparison. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma analytic_vanishing_isBigO (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) (h0 : f 0 = 0) :
    f =O[𝓝 (0:ℝ)] (fun δ : ℝ => δ) := by
  obtain ⟨F,hF,hF0,he⟩ := analytic_factor_at_zero f hf h0
  have hb : F =O[𝓝 (0:ℝ)] (fun _ => (1:ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto hF.continuousAt.tendsto one_ne_zero
  have ht := (Asymptotics.isBigO_refl (fun δ : ℝ => δ) (𝓝 (0:ℝ))).mul hb
  have heq : (fun δ => δ*F δ) =ᶠ[𝓝 (0:ℝ)] f := by
    filter_upwards [he] with δ hδ
    exact hδ.symm
  exact ht.congr' heq (by filter_upwards with δ;exact mul_one δ)
lemma action_weighted_identity (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    WP.action Y = 2*WP.Delta Y*Real.sqrt (WP.Delta Y)*
      stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) := by
  rw [stationaryWeighted_real_integral _ (by fun_prop) _ X_differentiable.deriv.continuous]
  have ht : Y < WP.T Y := lt_trans hY.2 (WP.stationary_root_proof Y hY).1.1
  simpa only [WP.action,WP.Delta,a] using WP.action_integral_square Y (WP.T Y) ht
lemma action_normalized_moment_identity (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    WP.action Y/((8*criticalB/45)*Real.rpow (WP.Delta Y) (5/2:ℝ)) =
      (stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)/WP.Delta Y)/((4/45)*criticalB) := by
  have hD := WP.Delta_pos Y hY
  have hS := Real.sqrt_pos.mpr hD
  have hB := criticalB_pos
  have hr : Real.rpow (WP.Delta Y) (5/2:ℝ) = (WP.Delta Y)^2*Real.sqrt (WP.Delta Y) := by
    rw [Real.rpow_eq_pow,show (5/2:ℝ) = 2+(1/2:ℝ) by ring,Real.rpow_add hD,Real.rpow_two,← Real.sqrt_eq_rpow]
  rw [action_weighted_identity Y hY,hr]
  field_simp [hD.ne',hS.ne',hB.ne'] <;> ring
lemma action_critical_error :
    (fun Y => WP.action Y/(8*criticalB/45*Real.rpow (WP.Delta Y) (5/2:ℝ))-1)
      =O[𝓝[<] y₀] WP.Delta := by
  obtain ⟨R,hR,hR0,heR⟩ := criticalMoment_over_Delta_factor
  let E : ℝ → ℝ := fun δ => R δ/((4/45)*criticalB)-1
  have hc : ((4/45:ℝ)*criticalB) ≠ 0 := mul_ne_zero (by norm_num) criticalB_pos.ne'
  have hE : AnalyticAt ℝ E 0 := hR.div_const.sub analyticAt_const
  have hE0 : E 0 = 0 := by dsimp [E];rw [hR0,div_self hc,sub_self]
  have ht := (analytic_vanishing_isBigO E hE hE0).comp_tendsto deltaCoordinate_tendsto
  have hm : ∀ᶠ Y in 𝓝[<] y₀,Y ∈ Ico 0 y₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    exact ⟨hpos.le,hY⟩
  have heq : (E ∘ fun Y : ℝ => y₀-Y) =ᶠ[𝓝[<] y₀]
      (fun Y => WP.action Y/(8*criticalB/45*Real.rpow (WP.Delta Y) (5/2:ℝ))-1) := by
    filter_upwards [criticalDelta_eq_actual,criticalMoment_eq_actual,
      deltaCoordinate_tendsto.eventually heR,hm] with Y hD hM hR hY
    have hn : y₀-Y ≠ 0 := sub_ne_zero.mpr (ne_of_gt hY.2)
    dsimp [Function.comp_def,E]
    have hN := action_normalized_moment_identity Y hY
    simp only [Real.rpow_eq_pow] at hN
    rw [hN,← hD,← hM,hR hn]
  exact (ht.congr' heq Filter.EventuallyEq.rfl).trans deltaCoordinate_isBigO_Delta
lemma stationaryMoment_over_Delta_tendsto :
    Tendsto (fun Y => stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)/WP.Delta Y)
      (𝓝[<] y₀) (𝓝 ((4/45)*criticalB)) := by
  obtain ⟨R,hR,hR0,he⟩ := criticalMoment_over_Delta_factor
  have ht := hR.continuousAt.tendsto.comp deltaCoordinate_tendsto
  have heq : (fun Y => R (y₀-Y)) =ᶠ[𝓝[<] y₀]
      (fun Y => stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)/WP.Delta Y) := by
    filter_upwards [criticalDelta_eq_actual,criticalMoment_eq_actual,deltaCoordinate_tendsto.eventually he,
      self_mem_nhdsWithin] with Y hD hM hR hY
    rw [← hD,← hM,hR (sub_ne_zero.mpr (ne_of_gt hY))]
  simpa only [hR0] using ht.congr' heq
lemma density_weighted_identity (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    WP.density Y = XR Y/(WP.Delta Y*stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)) := by
  have hD := WP.Delta_pos Y hY
  have hS := Real.sqrt_pos.mpr hD
  have hM : stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) ≠ 0 := by
    intro he
    have hp := WP.action_pos Y hY
    rw [action_weighted_identity Y hY,he,mul_zero] at hp
    exact lt_irrefl _ hp
  rw [WP.density,action_weighted_identity Y hY]
  field_simp [hD.ne',hS.ne',hM] <;> ring
lemma density_scaled_moment_identity (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    WP.density Y*(WP.Delta Y)^2 =
      XR Y/(stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)/WP.Delta Y) := by
  have hD := WP.Delta_pos Y hY
  have hM : stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) ≠ 0 := by
    intro he
    have hp := WP.action_pos Y hY
    rw [action_weighted_identity Y hY,he,mul_zero] at hp
    exact lt_irrefl _ hp
  rw [density_weighted_identity Y hY,div_div_eq_mul_div]
  field_simp [hD.ne',hM] <;> ring
lemma density_scaled_tendsto_critical :
    Tendsto (fun Y => WP.density Y*(WP.Delta Y)^2) (𝓝[<] y₀) (𝓝 (45*xCritical/(4*criticalB))) := by
  have hx : Tendsto XR (𝓝[<] y₀) (𝓝 xCritical) :=
    XR_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hc : ((4/45:ℝ)*criticalB) ≠ 0 := mul_ne_zero (by norm_num) criticalB_pos.ne'
  have ht := hx.div stationaryMoment_over_Delta_tendsto hc
  have heq : (fun Y => XR Y/(stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)/WP.Delta Y)) =ᶠ[𝓝[<] y₀]
      (fun Y => WP.density Y*(WP.Delta Y)^2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    exact (density_scaled_moment_identity Y ⟨hpos.le,hY⟩).symm
  have hv : xCritical/((4/45)*criticalB) = 45*xCritical/(4*criticalB) := by field_simp [criticalB_pos.ne'] <;> ring
  simpa only [hv] using ht.congr' heq
lemma density_critical_equivalence :
    Tendsto (fun Y => WP.density Y/(45*xCritical/(4*criticalB)*(WP.Delta Y)⁻¹^2))
      (𝓝[<] y₀) (𝓝 1) := by
  have hb := criticalB_pos
  have hx : 0 < xCritical := by
    change 0 < XR y₀
    rw [XR_eq_neg_mul_second]
    exact mul_pos y₀_pos criticalB_pos
  have hc : 45*xCritical/(4*criticalB) ≠ 0 := ne_of_gt (by positivity)
  have ht := density_scaled_tendsto_critical.div_const (45*xCritical/(4*criticalB))
  have heq : (fun Y => WP.density Y*(WP.Delta Y)^2/(45*xCritical/(4*criticalB))) =ᶠ[𝓝[<] y₀]
      (fun Y => WP.density Y/(45*xCritical/(4*criticalB)*(WP.Delta Y)⁻¹^2)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    have hD := WP.Delta_pos Y ⟨hpos.le,hY⟩
    field_simp [hc,hD.ne']
  simpa only [div_self hc] using ht.congr' heq
lemma densityY_spec (l : ℝ) (hl : 0 ≤ l) :
    WP.densityY l ∈ Ico 0 y₀ ∧ WP.density (WP.densityY l) = l := by
  obtain ⟨Y,hY,he⟩ := density_bijOn.surjOn hl
  have hset : {y : ℝ | y ∈ Ico 0 y₀ ∧ WP.density y = l} = {Y} := by
    ext y
    constructor
    · intro hy
      have heq := density_strictMonoOn.injOn hy.1 hY (hy.2.trans he.symm)
      simpa only [mem_singleton_iff] using heq
    · intro hy
      have heq : y = Y := mem_singleton_iff.mp hy
      subst y
      exact ⟨hY,he⟩
  have hi : WP.densityY l = Y := by unfold WP.densityY;rw [hset,csInf_singleton]
  rw [hi]
  exact ⟨hY,he⟩
lemma densityY_tendsto_critical : Tendsto WP.densityY atTop (𝓝[<] y₀) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_order.mpr ⟨?_,?_⟩,?_⟩
  · intro a ha
    by_cases hn : a < 0
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with l hl
      exact lt_of_lt_of_le hn (densityY_spec l hl).1.1
    · have hA : a ∈ Ico 0 y₀ := ⟨le_of_not_gt hn,ha⟩
      filter_upwards [eventually_ge_atTop (max (0:ℝ) (WP.density a+1))] with l hl
      have hl0 := le_trans (le_max_left _ _) hl
      have hld := le_trans (le_max_right _ _) hl
      have hs := densityY_spec l hl0
      by_contra h
      have he := density_strictMonoOn.monotoneOn hs.1 hA (le_of_not_gt h)
      rw [hs.2] at he
      linarith
  · intro b hb
    filter_upwards [eventually_ge_atTop (0:ℝ)] with l hl
    exact lt_trans (densityY_spec l hl).1.2 hb
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with l hl
    exact (densityY_spec l hl).1.2
lemma critical_x_pos : 0 < xCritical := by
  change 0 < XR y₀
  rw [XR_eq_neg_mul_second]
  exact mul_pos y₀_pos criticalB_pos
lemma profileC_critical_equivalence :
    Tendsto (fun l => WP.profileC l/(Real.pi^2/xCritical*l)) atTop (𝓝 1) := by
  have hx : Tendsto (fun l => XR (WP.densityY l)) atTop (𝓝 xCritical) :=
    XR_continuous.continuousAt.tendsto.comp (densityY_tendsto_critical.mono_right nhdsWithin_le_nhds)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => xCritical) atTop (𝓝 xCritical)).div hx critical_x_pos.ne'
  have heq : (fun l => xCritical/XR (WP.densityY l)) =ᶠ[atTop]
      (fun l => WP.profileC l/(Real.pi^2/xCritical*l)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with l hl
    rw [WP.profileC,if_neg hl.ne']
    field_simp [critical_x_pos.ne',Real.pi_ne_zero,hl.ne']
  simpa only [div_self critical_x_pos.ne'] using ht.congr' heq
lemma critical_density_constant_eq : 45*xCritical/(4*criticalB) = 45*y₀/4 := by
  have he : xCritical = y₀*criticalB := XR_eq_neg_mul_second y₀
  rw [he]
  field_simp [criticalB_pos.ne']
lemma critical_density_constant_sqrt :
    Real.sqrt (45*xCritical/(4*criticalB)) = 3*Real.sqrt 5*Real.sqrt y₀/2 := by
  have hy := y₀_pos
  rw [critical_density_constant_eq,show 45*y₀/4 = (9*5*y₀)/4 by ring,
    Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity : (0:ℝ) ≤ 9*5),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 9)]
  norm_num
lemma densityY_Delta_sqrt_tendsto :
    Tendsto (fun l => WP.Delta (WP.densityY l)*Real.sqrt l) atTop
      (𝓝 (Real.sqrt (45*xCritical/(4*criticalB)))) := by
  have ht := density_scaled_tendsto_critical.comp densityY_tendsto_critical
  have he : (fun l => WP.density (WP.densityY l)*(WP.Delta (WP.densityY l))^2) =ᶠ[atTop]
      (fun l => l*(WP.Delta (WP.densityY l))^2) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with l hl
    rw [(densityY_spec l hl).2]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (ht.congr' he)
  have heq : (fun l => Real.sqrt (l*(WP.Delta (WP.densityY l))^2)) =ᶠ[atTop]
      (fun l => WP.Delta (WP.densityY l)*Real.sqrt l) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with l hl
    rw [Real.sqrt_mul hl,Real.sqrt_sq_eq_abs,abs_of_pos (WP.Delta_pos _ (densityY_spec l hl).1),mul_comm]
  exact hs.congr' heq
lemma profileB_critical_equivalence :
    Tendsto (fun l => WP.profileB l/
      (Real.pi^2/(3*Real.sqrt 5*(2*Real.sqrt y₀))*Real.sqrt l)) atTop (𝓝 1) := by
  have hy := y₀_pos
  have hb := criticalB_pos
  have hx := critical_x_pos
  let C : ℝ := Real.pi^2/(3*Real.sqrt 5*(2*Real.sqrt y₀))
  have hC : 0 < C := by dsimp [C];positivity
  have hk : 0 < Real.sqrt (45*xCritical/(4*criticalB)) := by
    apply Real.sqrt_pos.mpr
    positivity
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi^2) atTop (𝓝 (Real.pi^2))).div
    (tendsto_const_nhds.mul densityY_Delta_sqrt_tendsto)
    (mul_ne_zero (show 4*C ≠ 0 by positivity) hk.ne')
  have hv : Real.pi^2/(4*C*Real.sqrt (45*xCritical/(4*criticalB))) = 1 := by
    rw [critical_density_constant_sqrt]
    dsimp [C]
    field_simp [(Real.sqrt_pos.mpr y₀_pos).ne',(Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<5)).ne',Real.pi_ne_zero] <;> ring
  have heq : (fun l => Real.pi^2/(4*C*(WP.Delta (WP.densityY l)*Real.sqrt l))) =ᶠ[atTop]
      (fun l => WP.profileB l/(C*Real.sqrt l)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with l hl
    have hD := WP.Delta_pos _ (densityY_spec l hl.le).1
    rw [WP.profileB]
    field_simp [hD.ne',(Real.sqrt_pos.mpr hl).ne',hC.ne'] <;> ring
  simpa only [hv] using ht.congr' heq
lemma Delta_tendsto_zero_critical : Tendsto WP.Delta (𝓝[<] y₀) (𝓝 0) := by
  have hi : Tendsto (fun Y : ℝ => Y) (𝓝[<] y₀) (𝓝 y₀) := tendsto_id.mono_left nhdsWithin_le_nhds
  simpa only [WP.Delta,sub_self] using! WP.T_tendsto_critical.sub hi
lemma oneMinusBeta_scaled_identity (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    (1-WP.beta Y)/(WP.Delta Y)^2 = 2/(2*(WP.Delta Y)^2+WP.density Y*(WP.Delta Y)^2) := by
  have hD := WP.Delta_pos Y hY
  have hP : 2+WP.density Y ≠ 0 := by linarith [WP.density_nonneg Y hY]
  rw [WP.beta_density_identity Y hY]
  have he : 2*(WP.Delta Y)^2+WP.density Y*(WP.Delta Y)^2 = (2+WP.density Y)*(WP.Delta Y)^2 := by ring
  rw [he]
  field_simp [hD.ne',hP] <;> ring
lemma oneMinusBeta_scaled_tendsto :
    Tendsto (fun Y => (1-WP.beta Y)/(WP.Delta Y)^2) (𝓝[<] y₀) (𝓝 (8*criticalB/(45*xCritical))) := by
  have hx := critical_x_pos
  have hb := criticalB_pos
  have hc : 45*xCritical/(4*criticalB) ≠ 0 := ne_of_gt (by positivity)
  have hz : Tendsto (fun Y => 2*(WP.Delta Y)^2) (𝓝[<] y₀) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero] using
      (Delta_tendsto_zero_critical.pow 2).const_mul 2
  have hd := hz.add density_scaled_tendsto_critical
  simp only [zero_add] at hd
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)) (𝓝[<] y₀) (𝓝 2)).div hd hc
  have heq : (fun Y => 2/(2*(WP.Delta Y)^2+WP.density Y*(WP.Delta Y)^2)) =ᶠ[𝓝[<] y₀]
      (fun Y => (1-WP.beta Y)/(WP.Delta Y)^2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    exact (oneMinusBeta_scaled_identity Y ⟨hpos.le,hY⟩).symm
  have hv : 2/(45*xCritical/(4*criticalB)) = 8*criticalB/(45*xCritical) := by field_simp [criticalB_pos.ne',critical_x_pos.ne'] <;> ring
  simpa only [hv] using ht.congr' heq
lemma sqrt_oneMinusBeta_over_Delta_tendsto :
    Tendsto (fun Y => Real.sqrt (1-WP.beta Y)/WP.Delta Y) (𝓝[<] y₀)
      (𝓝 (Real.sqrt (8*criticalB/(45*xCritical)))) := by
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp oneMinusBeta_scaled_tendsto
  have heq : (fun Y => Real.sqrt ((1-WP.beta Y)/(WP.Delta Y)^2)) =ᶠ[𝓝[<] y₀]
      (fun Y => Real.sqrt (1-WP.beta Y)/WP.Delta Y) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    have hY' : Y ∈ Ico 0 y₀ := ⟨hpos.le,hY⟩
    rw [Real.sqrt_div (sub_pos.mpr (WP.beta_lt_one Y hY')).le,
      Real.sqrt_sq_eq_abs,abs_of_pos (WP.Delta_pos Y hY')]
  exact ht.congr' heq
lemma Delta_beta_scale_bounds :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ Y in 𝓝[<] y₀,
      c*Real.sqrt (1-WP.beta Y) ≤ WP.Delta Y ∧ WP.Delta Y ≤ C*Real.sqrt (1-WP.beta Y) := by
  have hx := critical_x_pos
  have hb := criticalB_pos
  let k : ℝ := Real.sqrt (8*criticalB/(45*xCritical))
  have hk : 0 < k := by dsimp [k];positivity
  refine ⟨1/(2*k),2/k,by positivity,by positivity,?_⟩
  have he := sqrt_oneMinusBeta_over_Delta_tendsto.eventually
    (Ioo_mem_nhds (half_lt_self hk) (by linarith : k < 2*k))
  filter_upwards [he,self_mem_nhdsWithin,
    (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hlt hpos
  have hY' : Y ∈ Ico 0 y₀ := ⟨hpos.le,hlt⟩
  have hD := WP.Delta_pos Y hY'
  have hlo := (le_div_iff₀ hD).mp hY.1.le
  have hup := (div_le_iff₀ hD).mp hY.2.le
  constructor
  · rw [show 1/(2*k)*Real.sqrt (1-WP.beta Y) = Real.sqrt (1-WP.beta Y)/(2*k) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 2*k)).mpr
    nlinarith
  · rw [show (2/k)*Real.sqrt (1-WP.beta Y) = 2*Real.sqrt (1-WP.beta Y)/k by ring]
    apply (le_div_iff₀ hk).mpr
    nlinarith
theorem parameter_critical_proof :
    let b := -(iteratedDeriv 2 X y₀).re
    0 < b ∧ b = xCritical/y₀ ∧
    (fun Y => Delta Y - 3/2*(y₀-Y)) =O[𝓝[<] y₀] (fun Y => (y₀-Y)^2) ∧
    (fun Y => action Y / (8*b/45 * Real.rpow (Delta Y) (5/2 : ℝ)) - 1)
      =O[𝓝[<] y₀] Delta ∧
    Tendsto (fun Y => density Y / (45*xCritical/(4*b) * (Delta Y)⁻¹^2))
      (𝓝[<] y₀) (𝓝 1) ∧
    Tendsto (fun l => profileB l /
      (Real.pi^2/(3*Real.sqrt 5*(2*Real.sqrt y₀))*Real.sqrt l)) atTop (𝓝 1) ∧
    Tendsto (fun l => profileC l / (Real.pi^2/xCritical*l)) atTop (𝓝 1) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ Y in 𝓝[<] y₀,
      c*Real.sqrt (1-beta Y) ≤ Delta Y ∧ Delta Y ≤ C*Real.sqrt (1-beta Y)) := by
  dsimp only
  exact ⟨criticalB_pos,criticalB_eq,Delta_critical_error,action_critical_error,
    density_critical_equivalence,profileB_critical_equivalence,profileC_critical_equivalence,
    Delta_beta_scale_bounds⟩

end WP.Analysis
