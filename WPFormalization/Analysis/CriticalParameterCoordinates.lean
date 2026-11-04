import WPFormalization.Analysis.CriticalParameterDerivatives
import WPFormalization.Analysis.AnalyticFactors
import WPFormalization.Analysis.ParameterRegular

/-! Actual critical-coordinate factors, with the exact Delta and moment
first derivatives and the quadratic Delta remainder. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
def criticalB : ℝ := -(iteratedDeriv 2 X (y₀:ℂ)).re
lemma criticalB_pos : 0 < criticalB := by
  exact neg_pos.mpr (second_X_neg_before y₀ (by linarith [y₀_lt_three_halves]))
lemma criticalB_eq : criticalB = xCritical/y₀ := by
  apply (eq_div_iff y₀_pos.ne').mpr
  have he := XR_eq_neg_mul_second y₀
  change criticalB*y₀ = XR y₀
  rw [he]
  dsimp only [criticalB]
  ring
/-- The analytic continuation of Delta in the left endpoint coordinate δ=y₀−Y. -/
def criticalDelta (δ : ℝ) : ℝ := criticalStationaryBranch (y₀-δ)-(y₀-δ)
/-- The actual compact first moment along the local critical stationary germ. -/
def criticalMoment (δ : ℝ) : ℝ :=
  stationaryWeighted (fun s => s^2) (deriv X) (y₀-δ) (criticalStationaryBranch (y₀-δ))
lemma criticalDelta_analyticAt : AnalyticAt ℝ criticalDelta 0 := by
  have hb : AnalyticAt ℝ criticalStationaryBranch (y₀-(0:ℝ)) := by
    simpa only [sub_zero] using criticalStationaryBranch_analyticAt
  exact (hb.comp (analyticAt_const.sub analyticAt_id)).sub (analyticAt_const.sub analyticAt_id)
lemma criticalDelta_zero : criticalDelta 0 = 0 := by
  simp only [criticalDelta,sub_zero,criticalStationaryBranch_value,sub_self]
lemma criticalDelta_hasDerivAt : HasDerivAt criticalDelta (3/2) 0 := by
  have hs : HasDerivAt (fun δ : ℝ => y₀-δ) (-1) 0 := by
    simpa only [zero_sub,id_eq,Pi.sub_apply] using! (hasDerivAt_const (0:ℝ) y₀).sub (hasDerivAt_id 0)
  have hb : HasDerivAt criticalStationaryBranch (-1/2) y₀ := by
    rw [← criticalStationaryBranch_deriv_value]
    exact criticalStationaryBranch_analyticAt.differentiableAt.hasDerivAt
  have hb' : HasDerivAt criticalStationaryBranch (-1/2) (y₀-(0:ℝ)) := by simpa only [sub_zero] using hb
  convert! (hb'.comp 0 hs).sub hs using 1 <;> norm_num [criticalDelta,Function.comp_def]
lemma criticalMoment_analyticAt_zero : AnalyticAt ℝ criticalMoment 0 := by
  have hm : AnalyticAt ℝ (fun Y => stationaryWeighted (fun s => s^2) (deriv X) Y (criticalStationaryBranch Y)) (y₀-(0:ℝ)) := by
    simpa only [sub_zero] using criticalMoment_analyticAt
  exact hm.comp (analyticAt_const.sub analyticAt_id)
lemma criticalMoment_zero : criticalMoment 0 = 0 := by
  simpa only [criticalMoment,sub_zero] using criticalMoment_value
lemma criticalMoment_hasDerivAt_zero : HasDerivAt criticalMoment ((2/15)*criticalB) 0 := by
  have hs : HasDerivAt (fun δ : ℝ => y₀-δ) (-1) 0 := by
    simpa only [zero_sub,id_eq,Pi.sub_apply] using! (hasDerivAt_const (0:ℝ) y₀).sub (hasDerivAt_id 0)
  have hm : HasDerivAt (fun Y => stationaryWeighted (fun s => s^2) (deriv X) Y (criticalStationaryBranch Y))
      ((2/15:ℝ)*(deriv (deriv X) (y₀:ℂ)).re) (y₀-(0:ℝ)) := by
    simpa only [sub_zero] using criticalMoment_hasDerivAt
  convert! hm.comp 0 hs using 1 <;>
    simp only [criticalMoment,Function.comp_def,criticalB,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring
lemma criticalDelta_factor :
    ∃ D : ℝ → ℝ,AnalyticAt ℝ D 0 ∧ D 0 = 3/2 ∧ ∀ᶠ δ in 𝓝 0,criticalDelta δ = δ*D δ := by
  obtain ⟨D,hD,hD0,he⟩ := analytic_factor_at_zero criticalDelta criticalDelta_analyticAt criticalDelta_zero
  refine ⟨D,hD,?_,he⟩
  rw [hD0,criticalDelta_hasDerivAt.deriv]
lemma criticalMoment_over_Delta_factor :
    ∃ R : ℝ → ℝ,AnalyticAt ℝ R 0 ∧ R 0 = (4/45)*criticalB ∧
      ∀ᶠ δ in 𝓝 0,δ ≠ 0 → criticalMoment δ/criticalDelta δ = R δ := by
  have hd : deriv criticalDelta 0 ≠ 0 := by rw [criticalDelta_hasDerivAt.deriv];norm_num
  obtain ⟨R,hR,hR0,he⟩ := analytic_removable_ratio_at_zero criticalMoment criticalDelta
    criticalMoment_analyticAt_zero criticalDelta_analyticAt criticalMoment_zero criticalDelta_zero hd
  refine ⟨R,hR,?_,he⟩
  rw [hR0,criticalMoment_hasDerivAt_zero.deriv,criticalDelta_hasDerivAt.deriv]
  ring
lemma criticalDelta_eq_actual :
    (fun Y => criticalDelta (y₀-Y)) =ᶠ[𝓝[<] y₀] WP.Delta := by
  filter_upwards [T_eventually_eq_criticalStationaryBranch] with Y hY
  dsimp [criticalDelta,WP.Delta]
  rw [show y₀-(y₀-Y) = Y by ring,← hY]
lemma criticalMoment_eq_actual :
    (fun Y => criticalMoment (y₀-Y)) =ᶠ[𝓝[<] y₀]
      (fun Y => stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)) := by
  filter_upwards [T_eventually_eq_criticalStationaryBranch] with Y hY
  dsimp [criticalMoment]
  rw [show y₀-(y₀-Y) = Y by ring,← hY]
lemma deltaCoordinate_tendsto : Tendsto (fun Y : ℝ => y₀-Y) (𝓝[<] y₀) (𝓝 0) := by
  have hi : Tendsto (fun Y : ℝ => Y) (𝓝[<] y₀) (𝓝 y₀) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa only [sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => y₀) (𝓝[<] y₀) (𝓝 y₀)).sub hi
lemma Delta_over_delta_tendsto :
    Tendsto (fun Y => WP.Delta Y/(y₀-Y)) (𝓝[<] y₀) (𝓝 (3/2)) := by
  obtain ⟨D,hD,hD0,he⟩ := criticalDelta_factor
  have ht := hD.continuousAt.tendsto.comp deltaCoordinate_tendsto
  have heq : (fun Y => D (y₀-Y)) =ᶠ[𝓝[<] y₀] (fun Y => WP.Delta Y/(y₀-Y)) := by
    filter_upwards [criticalDelta_eq_actual,deltaCoordinate_tendsto.eventually he,self_mem_nhdsWithin] with Y hY hD hlt
    have hn : y₀-Y ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
    rw [← hY,hD,mul_div_cancel_left₀ _ hn]
  simpa only [hD0] using ht.congr' heq
lemma deltaCoordinate_isBigO_Delta : (fun Y : ℝ => y₀-Y) =O[𝓝[<] y₀] WP.Delta :=
  Asymptotics.isBigO_of_div_tendsto_nhds_of_ne_zero Delta_over_delta_tendsto (by norm_num)
lemma Delta_critical_error :
    (fun Y => WP.Delta Y-3/2*(y₀-Y)) =O[𝓝[<] y₀] (fun Y => (y₀-Y)^2) := by
  have he := analytic_first_order_error_at_zero criticalDelta criticalDelta_analyticAt
  rw [criticalDelta_zero,criticalDelta_hasDerivAt.deriv] at he
  have ht := he.comp_tendsto deltaCoordinate_tendsto
  apply ht.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [criticalDelta_eq_actual] with Y hY
  simp only [Function.comp_def,sub_zero,hY]

end WP.Analysis
