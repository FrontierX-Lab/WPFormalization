import WPFormalization.Analysis.CriticalParameterAsymptotics
import WPFormalization.Analysis.ParameterODE

/-! Exact parameter identities for the logarithmic diagonal-chain profile.
All functions here use the original stationary action and J integrals. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def chainClosedProfileY (Y : ℝ) : ℝ :=
  -2*Real.log (2*WP.J Y)-(1-WP.beta Y)*Real.log (4*WP.Delta Y/Real.pi^2)

lemma chain_Delta_hasDerivAt (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt WP.Delta (deriv WP.T Y-1) Y := by
  exact (T_analyticAt_interior Y hY).differentiableAt.hasDerivAt.sub (hasDerivAt_id Y)

lemma chain_J_Delta_derivative_identity (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    2*WP.Delta Y*deriv WP.J Y = -(WP.J Y-XR Y)*(deriv WP.T Y-1) := by
  have hJ := WP.J_action_identity Y hY
  have hI := action_weighted_identity Y hY
  have hs := (Real.sqrt_pos.mpr (WP.Delta_pos Y hY)).ne'
  have he : WP.J Y-XR Y = 2*WP.Delta Y*
      stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) := by
    rw [hI] at hJ
    field_simp [hs] at hJ
    nlinarith only [hJ]
  rw [J_deriv_interior Y hY,he]
  ring

lemma chainClosedProfileY_hasDerivAt (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt chainClosedProfileY
      (deriv WP.beta Y*Real.log (4*WP.Delta Y/Real.pi^2)) Y := by
  have hpJ := WP.J_pos Y hY
  have hpD := WP.Delta_pos Y hY
  have hJ := (J_analyticAt_interior Y hY).differentiableAt.hasDerivAt
  have hb := (beta_hasDerivAt_interior Y hY)
  have hb' : HasDerivAt WP.beta (deriv WP.beta Y) Y := by rwa [← hb.deriv] at hb
  have hlogJ := (hJ.const_mul 2).log (by positivity : 2*WP.J Y ≠ 0)
  have hlogD := (((chain_Delta_hasDerivAt Y hY).const_mul 4).div_const
    (Real.pi^2)).log (by positivity : 4*WP.Delta Y/Real.pi^2 ≠ 0)
  have hd := (hlogJ.const_mul (-2)).sub
    (((hasDerivAt_const Y (1 : ℝ)).sub hb').mul hlogD)
  convert hd using 1
  · rfl
  · have hrel := chain_J_Delta_derivative_identity Y hY
    simp only [Pi.sub_apply,WP.beta]
    field_simp [hpJ.ne',hpD.ne',Real.pi_ne_zero]
    nlinarith only [hrel]

lemma chainClosedProfileY_zero : chainClosedProfileY 0 = 0 := by
  have hD : WP.Delta 0 = Real.pi^2/4 := by simp [WP.Delta,WP.T_zero_value]
  have hquot : 4*(Real.pi^2/4)/Real.pi^2 = 1 := by field_simp
  simp [chainClosedProfileY,WP.J_zero_value,WP.beta_zero_value,hD,hquot]

lemma chain_J_deriv_pos (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < deriv WP.J Y := by
  have hI := WP.action_pos Y hY
  have hD := WP.Delta_pos Y hY
  have hS := Real.sqrt_pos.mpr hD
  have hM : 0 < stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) := by
    rw [action_weighted_identity Y hY] at hI
    exact (mul_pos_iff_of_pos_left (mul_pos (mul_pos (by norm_num) hD) hS)).mp hI
  rw [J_deriv_interior Y hY]
  exact mul_pos (by linarith [T_deriv_neg_interior Y hY]) hM

lemma chain_J_strictMonoOn : StrictMonoOn WP.J (Ico 0 y₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 y₀)
  · intro Y hY
    exact (J_analyticAt_interior Y hY).continuousAt.continuousWithinAt
  · intro Y hY
    exact chain_J_deriv_pos Y (interior_subset hY)

/-- The original density inverse is continuous even at the zero-density
boundary. This follows from the actual order isomorphism, with no choice
of an unrelated local inverse. -/
lemma chain_densityY_continuousOn : ContinuousOn WP.densityY (Ici 0) := by
  let f : Ico (0 : ℝ) y₀ → Ici (0 : ℝ) :=
    fun Y => ⟨WP.density Y,WP.density_nonneg Y Y.property⟩
  have hm : StrictMono f := by
    intro Y Z hYZ
    exact density_strictMonoOn Y.property Z.property hYZ
  have hs : Function.Surjective f := by
    intro l
    obtain ⟨Y,hY,he⟩ := density_bijOn.surjOn l.property
    exact ⟨⟨Y,hY⟩,Subtype.ext he⟩
  let e : Ico (0 : ℝ) y₀ ≃o Ici (0 : ℝ) := hm.orderIsoOfSurjective f hs
  have he : ∀ l : Ici (0 : ℝ), (e.symm l : ℝ) = WP.densityY l := by
    intro l
    apply density_strictMonoOn.injOn (e.symm l).property (densityY_spec l l.property).1
    have ht := congrArg Subtype.val (e.apply_symm_apply l)
    exact ht.trans (densityY_spec l l.property).2.symm
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc : Continuous (fun l : Ici (0 : ℝ) => (e.symm l : ℝ)) :=
    continuous_subtype_val.comp e.symm.continuous
  exact hc.congr he

lemma chain_densityY_density (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    WP.densityY (WP.density Y) = Y := by
  have hs := densityY_spec (WP.density Y) (WP.density_nonneg Y hY)
  exact density_strictMonoOn.injOn hs.1 hY hs.2

lemma chain_densityY_strictMonoOn : StrictMonoOn WP.densityY (Ici 0) := by
  intro l hl m hm hlm
  apply (density_strictMonoOn.lt_iff_lt (densityY_spec l hl).1
    (densityY_spec m hm).1).mp
  simpa only [(densityY_spec l hl).2,(densityY_spec m hm).2] using hlm

def chainCuspLogProfile (l : ℝ) : ℝ := -Real.log (2*WP.J (WP.densityY l))

lemma chainCuspLogProfile_antitoneOn : AntitoneOn chainCuspLogProfile (Ici 0) := by
  intro l hl m hm hlm
  have hYl := (densityY_spec l hl).1
  have hYm := (densityY_spec m hm).1
  apply neg_le_neg
  apply Real.log_le_log (mul_pos (by norm_num) (WP.J_pos _ hYl))
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact chain_J_strictMonoOn.monotoneOn hYl hYm
    (chain_densityY_strictMonoOn.monotoneOn hl hm hlm)

lemma chainCuspLogProfile_continuousOn : ContinuousOn chainCuspLogProfile (Ici 0) := by
  have hJ : ContinuousOn WP.J (Ico 0 y₀) :=
    fun Y hY => (J_analyticAt_interior Y hY).continuousAt.continuousWithinAt
  have hc := hJ.comp chain_densityY_continuousOn (fun l hl => (densityY_spec l hl).1)
  exact (continuousOn_const.mul hc).log (fun l hl => by
    exact (mul_pos (by norm_num) (WP.J_pos _ (densityY_spec l hl).1)).ne') |>.neg

lemma chainCuspLogProfile_zero : chainCuspLogProfile 0 = 0 := by
  have hd : WP.densityY 0 = 0 := by
    simpa only [WP.density_zero_value] using chain_densityY_density 0 ⟨le_rfl,y₀_pos⟩
  simp [chainCuspLogProfile,hd,WP.J_zero_value]

lemma chainCuspLogProfile_tendsto :
    Tendsto chainCuspLogProfile atTop (𝓝 (-Real.log (2*xCritical))) := by
  have hJ := J_tendsto_critical.comp densityY_tendsto_critical
  exact ((hJ.const_mul 2).log (mul_pos (by norm_num) critical_x_pos).ne').neg

lemma chainCuspLogProfile_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℝ, 0 ≤ l → chainCuspLogProfile 0-chainCuspLogProfile l ≤ C := by
  refine ⟨|Real.log (2*xCritical)|+1,by positivity,?_⟩
  intro l hl
  have hb : -Real.log (2*xCritical) ≤ chainCuspLogProfile l := by
    apply le_of_tendsto chainCuspLogProfile_tendsto
    filter_upwards [eventually_ge_atTop l,eventually_ge_atTop (0 : ℝ)] with m hm hm0
    exact chainCuspLogProfile_antitoneOn hl hm0 hm
  rw [chainCuspLogProfile_zero]
  linarith [le_abs_self (Real.log (2*xCritical))]

lemma chainCuspLogProfile_eq_log_profileC (l : ℝ) (hl : 0 ≤ l) :
    chainCuspLogProfile l = Real.log (2*WP.profileC l/(4*Real.pi^2*(2+l))) := by
  by_cases he : l = 0
  · subst l
    rw [chainCuspLogProfile_zero]
    simp only [WP.profileC,ite_true]
    have hr : 2*(4*Real.pi^2)/(4*Real.pi^2*(2+(0 : ℝ))) = 1 := by field_simp <;> ring
    rw [hr,Real.log_one]
  have hs := densityY_spec l hl
  have hx : 0 < XR (WP.densityY l) := by
    have hpos : 0 < WP.densityY l := by
      have hm := chain_densityY_strictMonoOn (show (0 : ℝ) ∈ Ici 0 from by simp) hl
        (lt_of_le_of_ne hl (Ne.symm he))
      have hz : WP.densityY 0 = 0 := by
        simpa only [WP.density_zero_value] using chain_densityY_density 0 ⟨le_rfl,y₀_pos⟩
      rwa [hz] at hm
    exact (bessel_signs_pi_interval.1 _ ⟨hpos,
      le_trans hs.1.2.le (by nlinarith [y₀_lt_three_halves,Real.pi_gt_three])⟩)
  have hb := WP.beta_density_identity _ hs.1
  rw [hs.2,WP.beta] at hb
  have hJ := WP.J_pos _ hs.1
  have hden : 2+l ≠ 0 := by positivity
  have hr : 2*WP.profileC l/(4*Real.pi^2*(2+l)) = (2*WP.J (WP.densityY l))⁻¹ := by
    rw [WP.profileC,if_neg he]
    have heq := (div_eq_div_iff hJ.ne' hden).mp hb
    field_simp [hx.ne',hJ.ne',hden,Real.pi_ne_zero]
    nlinarith only [heq]
  rw [hr,Real.log_inv]
  rfl

lemma chain_profileC_pos (l : ℝ) (hl : 0 ≤ l) : 0 < WP.profileC l := by
  by_cases he : l = 0
  · simp only [WP.profileC,he,ite_true]
    positivity
  have hs := densityY_spec l hl
  have hd := density_J_formula_on_domain _ (stationaryParameterDomain_contains _ hs.1)
  rw [hs.2] at hd
  have hJX := J_sub_XR_pos_interior _ hs.1
  have hlp : 0 < l := lt_of_le_of_ne hl (Ne.symm he)
  have hx : 0 < XR (WP.densityY l) := by
    have hp : 0 < 2*XR (WP.densityY l) :=
      (div_pos_iff_of_pos_right hJX).mp (hd ▸ hlp)
    linarith
  simp only [WP.profileC,he,ite_false]
  positivity

end WP.Analysis
