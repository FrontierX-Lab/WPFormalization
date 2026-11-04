import WPFormalization.Analysis.CriticalKernelLipschitz
import WPFormalization.Statements.Marked
/-! Genuine critical scale of the original normalized action Z.
The actual left factors a/δ→b, r/δ→3 and A→2/15 give
Z/δ^(5/2)→(2/15)*b*3^(3/2). Positive two-sided power bounds and
an additive logarithmic bound follow. The proofs use only standard axioms;
the first root at the critical parameter is never evaluated. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace WP.Analysis
lemma A_tendsto_critical_value : Tendsto A (𝓝[<] y₀) (𝓝 (2/15:ℝ)) := by
  have ht0 : Tendsto (fun Y : ℝ => Y-y₀) (𝓝[<] y₀) (𝓝 0) := by
    simpa only [sub_self,id_eq] using
      (tendsto_id.mono_left (show 𝓝[<] y₀ ≤ 𝓝 y₀ from nhdsWithin_le_nhds)).sub_const y₀
  have ht := A_critical_isBigO.trans_tendsto ht0
  simpa only [sub_add_cancel,zero_add] using ht.add_const (2/15:ℝ)

lemma a_div_delta_tendsto_critical :
    Tendsto (fun Y => a Y/(y₀-Y)) (𝓝[<] y₀) (𝓝 criticalB) := by
  obtain ⟨F,hF,hF0,he⟩ := analytic_factor_at_zero (fun δ : ℝ => a (y₀-δ))
    critical_a_coordinate_analyticAt (by simp only [sub_zero,a_y₀_zero])
  rw [critical_a_coordinate_hasDerivAt.deriv] at hF0
  have ht := hF.continuousAt.tendsto.comp deltaCoordinate_tendsto
  rw [hF0] at ht
  apply ht.congr'
  filter_upwards [deltaCoordinate_tendsto.eventually he,self_mem_nhdsWithin] with Y hF hY
  rw [show y₀-(y₀-Y)=Y by ring] at hF
  dsimp only [Function.comp_def]
  rw [hF,mul_div_cancel_left₀ _ (sub_ne_zero.mpr (ne_of_gt hY))]

lemma r_div_delta_tendsto_critical :
    Tendsto (fun Y => r Y/(y₀-Y)) (𝓝[<] y₀) (𝓝 (3:ℝ)) := by
  have ht := Delta_over_delta_tendsto.const_mul 2
  have he : (fun Y => 2*(Delta Y/(y₀-Y))) =ᶠ[𝓝[<] y₀] (fun Y => r Y/(y₀-Y)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    rw [(stationary_root_proof Y ⟨hpos.le,hY⟩).2.2.2]
    ring
  convert ht.congr' he using 1 <;> norm_num

lemma normalized_action_scale_identity (A a r δ : ℝ) (hδ : 0 < δ) (hr : 0 < r) :
    A*a*Real.rpow r (3/2:ℝ)/Real.rpow δ (5/2:ℝ) =
      A*(a/δ)*Real.rpow (r/δ) (3/2:ℝ) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow hr.le hδ.le,show (5/2:ℝ)=1+(3/2:ℝ) by ring,
    Real.rpow_add hδ,Real.rpow_one]
  field_simp [hδ.ne',(Real.rpow_pos_of_pos hδ (3/2:ℝ)).ne']

lemma Z_scaled_tendsto_critical :
    Tendsto (fun Y => Z Y/Real.rpow (y₀-Y) (5/2:ℝ)) (𝓝[<] y₀)
      (𝓝 ((2/15:ℝ)*criticalB*Real.rpow 3 (3/2:ℝ))) := by
  have hpow := r_div_delta_tendsto_critical.rpow_const (Or.inl (by norm_num : (3:ℝ)≠0))
    (p := (3/2:ℝ))
  have ht := (A_tendsto_critical_value.mul a_div_delta_tendsto_critical).mul hpow
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
  exact (normalized_action_scale_identity (A Y) (a Y) (r Y) (y₀-Y)
    (sub_pos.mpr hY) (r_pos Y ⟨hpos.le,hY⟩)).symm
end WP.Analysis
namespace WP.Analysis
lemma Z_critical_power_bounds :
    ∃ c C δ₀ : ℝ,0 < c ∧ 0 < C ∧ 0 < δ₀ ∧
      ∀ Y ∈ Ico (0:ℝ) y₀,y₀-Y ≤ δ₀ →
        c*Real.rpow (y₀-Y) (5/2:ℝ) ≤ Z Y ∧
        Z Y ≤ C*Real.rpow (y₀-Y) (5/2:ℝ) := by
  let L : ℝ := (2/15:ℝ)*criticalB*Real.rpow 3 (3/2:ℝ)
  have hL : 0 < L := mul_pos (mul_pos (by norm_num) criticalB_pos)
    (Real.rpow_pos_of_pos (by norm_num) _)
  have he := Z_scaled_tendsto_critical.eventually (Ioo_mem_nhds (half_lt_self hL) (by linarith : L < 2*L))
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨L/2,2*L,ε/2,by positivity,by positivity,by positivity,?_⟩
  intro Y hY hδ
  have hd : dist Y y₀ < ε := by
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hY.2)]
    linarith
  have hh := he hd hY.2
  have hp := Real.rpow_pos_of_pos (sub_pos.mpr hY.2) (5/2:ℝ)
  exact ⟨(le_div_iff₀ hp).mp hh.1.le,(div_le_iff₀ hp).mp hh.2.le⟩

lemma Z_critical_log_bound :
    ∃ M δ₀ : ℝ,0 < M ∧ 0 < δ₀ ∧ ∀ Y ∈ Ico (0:ℝ) y₀,y₀-Y ≤ δ₀ →
      |Real.log (Z Y)-(5/2:ℝ)*Real.log (y₀-Y)| ≤ M := by
  obtain ⟨c,C,δ,hc,hC,hδ,hb⟩ := Z_critical_power_bounds
  refine ⟨|Real.log c|+|Real.log C|+1,δ,by positivity,hδ,?_⟩
  intro Y hY hsmall
  have hδp := Real.rpow_pos_of_pos (sub_pos.mpr hY.2) (5/2:ℝ)
  have hZ : 0 < Z Y := lt_of_lt_of_le (mul_pos hc hδp) (hb Y hY hsmall).1
  have hlo : c ≤ Z Y/Real.rpow (y₀-Y) (5/2:ℝ) := (le_div_iff₀ hδp).mpr (hb Y hY hsmall).1
  have hup : Z Y/Real.rpow (y₀-Y) (5/2:ℝ) ≤ C := (div_le_iff₀ hδp).mpr (hb Y hY hsmall).2
  have hl := Real.log_le_log hc hlo
  have hu := Real.log_le_log (div_pos hZ hδp) hup
  have hlog : Real.log (Z Y/Real.rpow (y₀-Y) (5/2:ℝ)) =
      Real.log (Z Y)-(5/2:ℝ)*Real.log (y₀-Y) := by
    rw [Real.rpow_eq_pow,Real.log_div hZ.ne' hδp.ne',Real.log_rpow (sub_pos.mpr hY.2)]
  simp only [Real.rpow_eq_pow] at hlog hl hu
  rw [hlog] at hl hu
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log c),abs_nonneg (Real.log C)]
  · linarith [le_abs_self (Real.log C),abs_nonneg (Real.log c)]
end WP.Analysis
