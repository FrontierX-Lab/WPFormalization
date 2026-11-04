import WPFormalization.Statements.ParameterDefinitions
import WPFormalization.Analysis.ActionPositivity

/-! Proven components of Lemma3.1 for the original stationary parameter.
All functions use the original integral/infimum definitions. The main root
statement and action/J/beta identities are proved before the remaining
analyticity, derivative and asymptotic obligations are assembled.
-/
noncomputable section
namespace WP
open MeasureTheory Set Filter
open scoped Topology
theorem stationary_root_proof (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    T Y ∈ Set.Ioc y₀ (Real.pi^2/4) ∧ stationaryIntegral Y (T Y) = 0 ∧
    (∀ t ∈ Set.Ioc y₀ (Real.pi^2/4), stationaryIntegral Y t = 0 → t = T Y) ∧
    r Y = 2*Delta Y := by
  have hT : T Y = Y+r Y/2 := by
    unfold T
    rw [if_neg (ne_of_lt hY.2)]
    simpa only [stationaryIntegral] using stationary_sInf_eq_firstKernelEndpoint Y hY
  have hs := stationary_firstKernelEndpoint_unique Y hY
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hT] using hs.1
  · simpa only [stationaryIntegral,hT] using hs.2.1
  · intro t ht he
    have heq := hs.2.2 t ht he
    simpa only [hT] using heq
  · unfold Delta
    rw [hT]
    ring


lemma T_eq_firstKernelEndpoint (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : T Y = Y+r Y/2 := by
  have he : r Y = 2*(T Y-Y) := (stationary_root_proof Y hY).2.2.2
  linarith
lemma Delta_pos (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 < Delta Y := by
  unfold Delta
  have ht := (stationary_root_proof Y hY).1.1
  linarith [hY.2]
lemma action_pos (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 < action Y := by
  have hs := stationary_root_proof Y hY
  have hYT : Y < T Y := lt_trans hY.2 hs.1.1
  have hroot := (stationary_zero_iff_K_zero Y (T Y) hYT).mp hs.2.1
  exact stationary_action_pos Y (T Y) hY hs.1 hroot
lemma J_action_identity (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    J Y = XR Y+action Y/Real.sqrt (Delta Y) := by
  have hYT : Y < T Y := lt_trans hY.2 (stationary_root_proof Y hY).1.1
  simpa only [J,action,Delta] using J_action_integral Y (T Y) hYT
lemma T_continuous_interior : Continuous (fun Y : Set.Ico 0 y₀ => T (Y : ℝ)) := by
  have he : (fun Y : Set.Ico 0 y₀ => T (Y : ℝ)) = fun Y : Set.Ico 0 y₀ => (Y : ℝ)+r Y/2 := by
    funext Y
    exact T_eq_firstKernelEndpoint Y Y.property
  rw [he]
  exact continuous_subtype_val.add (Analysis.r_continuous_interior.div_const 2)
lemma T_tendsto_critical : Tendsto T (𝓝[<] y₀) (𝓝 y₀) := by
  have hmem : ∀ᶠ Y in 𝓝[<] y₀, Y ∈ Set.Ico 0 y₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    exact ⟨hpos.le,hY⟩
  have he : (fun Y => Y+r Y/2) =ᶠ[𝓝[<] y₀] T := by
    filter_upwards [hmem] with Y hY
    exact (T_eq_firstKernelEndpoint Y hY).symm
  have hi : Tendsto (fun Y : ℝ => Y) (𝓝[<] y₀) (𝓝 y₀) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have ht := hi.add (Analysis.r_tendsto_zero_left.div_const 2)
  simpa using ht.congr' he
lemma T_zero_value : T 0 = Real.pi^2/4 := by
  have hY : (0 : ℝ) ∈ Set.Ico 0 y₀ := ⟨le_rfl,y₀_pos⟩
  have hzero : K 0 ((Real.pi^2/2 : ℝ) : ℂ) = 0 := by
    have hs := Analysis.rootKernel_sine (Real.pi : ℂ)
    have hsin : Complex.sin (Real.pi : ℂ) = 0 := by rw [← Complex.ofReal_sin,Real.sin_pi,Complex.ofReal_zero]
    rw [hsin] at hs
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hr := (mul_eq_zero.mp hs).resolve_left hp
    simpa only [K,Analysis.rootKernel,Complex.ofReal_zero,Complex.ofReal_div,
      Complex.ofReal_pow,Complex.ofReal_ofNat] using hr
  have hr := Analysis.K_zero_unique_interval 0 (Real.pi^2/2) hY
    ⟨by positivity,by simp⟩ hzero
  rw [T_eq_firstKernelEndpoint 0 hY,← hr]
  ring

lemma XR_nonneg_interior (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 ≤ XR Y := by
  by_cases he : Y = 0
  · simp [he,XR,X]
  · have hp : y₀ < Real.pi^2/4 := by nlinarith [y₀_lt_three_halves,Real.pi_gt_three]
    exact (bessel_signs_pi_interval.1 Y
      ⟨lt_of_le_of_ne hY.1 (Ne.symm he),le_trans hY.2.le hp.le⟩).le
lemma J_pos (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 < J Y := by
  rw [J_action_identity Y hY]
  exact add_pos_of_nonneg_of_pos (XR_nonneg_interior Y hY)
    (div_pos (action_pos Y hY) (Real.sqrt_pos.mpr (Delta_pos Y hY)))
lemma density_nonneg (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 ≤ density Y := by
  unfold density
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (XR_nonneg_interior Y hY))
    (Real.sqrt_nonneg _)) (action_pos Y hY).le
lemma beta_density_identity (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    beta Y = density Y/(2+density Y) := by
  unfold beta
  have hden : (2 : ℝ)+density Y ≠ 0 := by linarith [density_nonneg Y hY]
  apply (div_eq_div_iff (ne_of_gt (J_pos Y hY)) hden).mpr
  rw [J_action_identity Y hY]
  unfold density
  have hI : action Y ≠ 0 := ne_of_gt (action_pos Y hY)
  have hs : Real.sqrt (Delta Y) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Delta_pos Y hY))
  field_simp [hI,hs]
  ring
lemma beta_nonneg (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 ≤ beta Y :=
  div_nonneg (XR_nonneg_interior Y hY) (J_pos Y hY).le
lemma beta_lt_one (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : beta Y < 1 := by
  rw [beta_density_identity Y hY]
  exact (div_lt_one (by linarith [density_nonneg Y hY])).mpr (by linarith)

end WP
