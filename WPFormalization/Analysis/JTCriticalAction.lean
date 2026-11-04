import WPFormalization.Analysis.JTCriticalUnits
import WPFormalization.Analysis.JTCriticalConstants

/-! The exact JT critical-action constants and relative remainders in both
δ=y₀−Y and xCritical−XR(Y). All statements concern the original full action. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace WP.Analysis

lemma jt_delta_isBigO_sqrt_gap :
    (fun Y : ℝ => y₀-Y) =O[𝓝[<] y₀] (fun Y => Real.sqrt (xCritical-XR Y)) := by
  obtain ⟨B,F,hB,hF,hB0,hF0,he⟩ := jt_critical_units_left
  have ht := (hB.continuousAt.tendsto.comp deltaCoordinate_tendsto).sqrt
  rw [hB0] at ht
  have hs : Tendsto (fun Y => Real.sqrt (xCritical-XR Y)/(y₀-Y)) (𝓝[<] y₀)
      (𝓝 (Real.sqrt (criticalB/2))) := by
    apply ht.congr'
    filter_upwards [he,self_mem_nhdsWithin] with Y h hY
    have hd : 0 < y₀-Y := sub_pos.mpr hY
    dsimp only [Function.comp_def]
    rw [h.1,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hd]
    field_simp
  exact Asymptotics.isBigO_of_div_tendsto_nhds_of_ne_zero hs
    (Real.sqrt_pos.mpr (div_pos criticalB_pos (by norm_num))).ne'

lemma jt_action_relative_delta :
    (fun Y => Z Y/((2*Real.sqrt 3*criticalB/5)*Real.rpow (y₀-Y) (5/2:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y) := by
  have he := jt_action_relative_delta_unsimplified
  simp only [Real.rpow_eq_pow,jt_critical_delta_constant] at he ⊢
  exact he

/-- The paper's exact coefficient of (x_c-x)^(5/4). -/
def jtCriticalActionConstant : ℝ :=
  Real.rpow 2 (9/4:ℝ)*Real.sqrt 3/(5*Real.rpow criticalB (1/4:ℝ))

lemma jtCriticalActionConstant_pos : 0 < jtCriticalActionConstant := by
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.sqrt_pos.mpr (by norm_num)))
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos criticalB_pos _))

/-- The leading critical power, with the exact paper coefficient. -/
def jtCriticalAction (Y : ℝ) : ℝ :=
  jtCriticalActionConstant*Real.rpow (xCritical-XR Y) (5/4:ℝ)

lemma jtCriticalAction_pos (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) :
    0 < jtCriticalAction Y := by
  have hgap : 0 < xCritical-XR Y :=
    sub_pos.mpr (XR_strictMonoOn hY.2.le (by simp) hY.2)
  exact mul_pos jtCriticalActionConstant_pos (Real.rpow_pos_of_pos hgap _)

lemma jt_action_relative_gap :
    (fun Y => Z Y/jtCriticalAction Y-1)
      =O[𝓝[<] y₀] (fun Y => Real.sqrt (xCritical-XR Y)) := by
  obtain ⟨B,F,hB,hF,hB0,hF0,he⟩ := jt_critical_units_left
  have hb : 0 < B 0 := by rw [hB0]; exact div_pos criticalB_pos (by norm_num)
  let L : ℝ := (2/15:ℝ)*criticalB*Real.rpow 3 (3/2:ℝ)
  have hL : 0 < L := mul_pos (mul_pos (by norm_num) criticalB_pos)
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hc : jtCriticalActionConstant = L/Real.rpow (criticalB/2) (5/4:ℝ) := by
    simpa only [jtCriticalActionConstant,L,Real.rpow_eq_pow] using
      (jt_critical_gap_constant criticalB criticalB_pos).symm
  let G : ℝ → ℝ := fun δ => F δ/(jtCriticalActionConstant*Real.rpow (B δ) (5/4:ℝ))
  have hg : DifferentiableAt ℝ G 0 :=
    hF.div ((hB.rpow_const (Or.inl hb.ne')).const_mul jtCriticalActionConstant)
      (mul_pos jtCriticalActionConstant_pos (Real.rpow_pos_of_pos hb _)).ne'
  have hg0 : G 0=1 := by
    dsimp only [G]
    rw [hF0,hB0,hc]
    change L/(L/Real.rpow (criticalB/2) (5/4:ℝ)*Real.rpow (criticalB/2) (5/4:ℝ))=1
    have hn := (Real.rpow_pos_of_pos
      (div_pos criticalB_pos (by norm_num : (0:ℝ)<2)) (5/4:ℝ)).ne'
    simp only [Real.rpow_eq_pow] at hn ⊢
    field_simp [hn,hL.ne']
  have ho := hg.hasDerivAt.isBigO_sub
  rw [hg0] at ho
  have ht := ho.comp_tendsto deltaCoordinate_tendsto
  have hdelta : (fun Y => Z Y/jtCriticalAction Y-1) =O[𝓝[<] y₀] (fun Y => y₀-Y) := by
    apply ht.congr' ?_ (by filter_upwards with Y; simp)
    filter_upwards [he,self_mem_nhdsWithin,
      (hB.continuousAt.tendsto.comp deltaCoordinate_tendsto).eventually
        (eventually_gt_nhds hb)] with Y h hY hBp
    have hd : 0 < y₀-Y := sub_pos.mpr hY
    dsimp only [Function.comp_def,G,jtCriticalAction]
    rw [h.1,h.2]
    have hpow := jt_gap_power_factor (y₀-Y) (B (y₀-Y)) hd.le hBp.le
    simp only [Real.rpow_eq_pow] at hpow ⊢
    rw [hpow]
    have hn := (Real.rpow_pos_of_pos hd (5/2:ℝ)).ne'
    field_simp [hn]
  exact hdelta.trans jt_delta_isBigO_sqrt_gap

lemma jt_sqrt_gap_tendsto_zero :
    Tendsto (fun Y => Real.sqrt (xCritical-XR Y)) (𝓝[<] y₀) (𝓝 (0:ℝ)) := by
  have hx : Tendsto XR (𝓝[<] y₀) (𝓝 xCritical) :=
    (XR_analyticAt y₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [sub_self,Real.sqrt_zero] using hx.const_sub xCritical |>.sqrt

/-- The same gap-coordinate estimate with x itself as the independent
variable on the genuine inverse branch, rather than a new local model. -/
lemma jt_action_relative_x :
    (fun x => Z (inverseY x)/(jtCriticalActionConstant*Real.rpow (xCritical-x) (5/4:ℝ))-1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (xCritical-x)) := by
  have hbranch : ∀ᶠ x : ℝ in 𝓝[<] xCritical,
      inverseY x ∈ Ico (0:ℝ) y₀ ∧ XR (inverseY x)=x := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds critical_x_pos).filter_mono nhdsWithin_le_nhds] with x hx hpos
    exact inverseY_branch x ⟨hpos.le,hx⟩
  have ht : Tendsto inverseY (𝓝[<] xCritical) (𝓝[<] y₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨inverseY_tendsto_critical_left,?_⟩
    filter_upwards [hbranch] with x hx
    exact hx.1.2
  have ho := jt_action_relative_gap.comp_tendsto ht
  apply ho.congr'
  · filter_upwards [hbranch] with x hx
    dsimp only [Function.comp_def,jtCriticalAction]
    rw [hx.2]
  · filter_upwards [hbranch] with x hx
    dsimp only [Function.comp_def]
    rw [hx.2]

lemma jt_action_log_relative_gap :
    (fun Y => Real.log (Z Y/jtCriticalAction Y))
      =O[𝓝[<] y₀] (fun Y => Real.sqrt (xCritical-XR Y)) := by
  have he := jt_action_relative_gap.trans_tendsto jt_sqrt_gap_tendsto_zero
  have ht : Tendsto (fun Y => Z Y/jtCriticalAction Y) (𝓝[<] y₀) (𝓝 (1:ℝ)) := by
    simpa only [sub_add_cancel,zero_add] using he.add_const 1
  have hl := (Real.hasDerivAt_log (show (1:ℝ)≠0 by norm_num)).isBigO_sub.comp_tendsto ht
  have ho := hl.trans jt_action_relative_gap
  simpa only [Function.comp_def,Real.log_one,sub_zero] using ho

end WP.Analysis
