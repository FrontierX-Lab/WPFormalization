import WPFormalization.Analysis.CriticalParameterAsymptotics
import WPFormalization.Analysis.ParameterODE
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

lemma volume_profile_J_deriv_bounds (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    0 ≤ deriv J Y ∧ deriv J Y ≤ 2*a Y/3 := by
  refine ⟨?_, J_deriv_upper_interior Y hY⟩
  rw [J_deriv_interior Y hY, stationary_first_moment_eq_Aa Y hY]
  have hA : 0 < A Y := by
    unfold A
    exact div_pos (barH_one_re_pos Y ⟨hY.1,hY.2.le⟩) (by norm_num)
  exact mul_nonneg (by linarith [T_deriv_neg_interior Y hY])
    (mul_nonneg hA.le (a_pos Y hY).le)

lemma volume_profile_A_le_third (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : A Y ≤ 1/3 := by
  have hm := stationary_first_moment_le Y hY
  rw [stationary_first_moment_eq_Aa Y hY] at hm
  have ha := a_pos Y hY
  nlinarith

/-- The stationary density controls its physical coordinate uniformly, with no
endpoint asymptotic premise. -/
lemma volume_profile_density_jacobian (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    1+density Y ≤ r Y*deriv density Y := by
  have ha := a_pos Y hY
  have hr := r_pos Y hY
  have hx := XR_nonneg_interior Y hY
  have hD := J_sub_XR_pos_interior Y hY
  have hJ := J_pos Y hY
  have hd := (volume_profile_J_deriv_bounds Y hY).2
  have hA := volume_profile_A_le_third Y hY
  have hAr := J_sub_XR_eq_Aar Y hY
  have hDr : 3*(J Y-XR Y) ≤ a Y*r Y := by
    have hmul := mul_le_mul_of_nonneg_right hA (mul_nonneg ha.le hr.le)
    nlinarith [hmul]
  rw [density_J_formula_on_domain Y (stationaryParameterDomain_contains Y hY),
    (density_hasDerivAt_interior Y hY).deriv]
  conv_rhs => rw [← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).2
  have he : (1+2*XR Y/(J Y-XR Y))*(J Y-XR Y)^2 =
      (J Y+XR Y)*(J Y-XR Y) := by
    field_simp
    <;> ring
  rw [he]
  have hnum : a Y*J Y/3 ≤ a Y*J Y-XR Y*deriv J Y := by
    have hh := mul_le_mul_of_nonneg_left hd hx
    have hh' := mul_nonneg ha.le hD.le
    nlinarith
  have hn := mul_le_mul_of_nonneg_left hnum hr.le
  have hscale := mul_le_mul_of_nonneg_right hDr hJ.le
  have hfinal := mul_nonneg hD.le hD.le
  nlinarith

def volumeProfileBPhysical (Y : ℝ) : ℝ := Real.pi^2/(2*r Y)
def volumeProfileCPhysical (Y : ℝ) : ℝ := 2*Real.pi^2/(J Y-XR Y)

lemma volume_profile_inverse_density (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    densityY (density Y) = Y := by
  have hs := densityY_spec (density Y) (density_nonneg Y hY)
  exact density_strictMonoOn.injOn hs.1 hY hs.2

lemma volume_profile_densityY_zero : densityY 0 = 0 := by
  simpa only [density_zero_value] using volume_profile_inverse_density 0 ⟨le_rfl,y₀_pos⟩

lemma volume_profile_B_physical (l : ℝ) (hl : 0 ≤ l) :
    profileB l = volumeProfileBPhysical (densityY l) := by
  have hs := (densityY_spec l hl).1
  have he := T_eq_firstKernelEndpoint _ hs
  unfold profileB volumeProfileBPhysical Delta
  congr 1
  linarith

lemma volume_profile_C_physical (l : ℝ) (hl : 0 ≤ l) :
    profileC l = volumeProfileCPhysical (densityY l) := by
  have hs := densityY_spec l hl
  have hD := J_sub_XR_pos_interior _ hs.1
  by_cases hz : l = 0
  · subst l
    norm_num [profileC,volume_profile_densityY_zero,
      volumeProfileCPhysical,J_zero_value,XR_zero]
    <;> ring
  · have hpos : 0 < l := lt_of_le_of_ne hl (Ne.symm hz)
    have he := density_J_formula_on_domain (densityY l) (stationaryParameterDomain_contains _ hs.1)
    rw [hs.2] at he
    have hxn : XR (densityY l) ≠ 0 := by
      intro hx
      rw [hx,mul_zero,zero_div] at he
      exact hz he
    simp only [profileC,if_neg hz,volumeProfileCPhysical]
    calc
      l*Real.pi^2/XR (densityY l) =
          (2*XR (densityY l)/(J (densityY l)-XR (densityY l)))*Real.pi^2/XR (densityY l) := by
        exact congrArg (fun t => t*Real.pi^2/XR (densityY l)) he
      _ = _ := by field_simp <;> ring

lemma volume_profile_B_pos (l : ℝ) (hl : 0 ≤ l) : 0 < profileB l := by
  rw [volume_profile_B_physical l hl]
  exact div_pos (sq_pos_of_pos Real.pi_pos) (mul_pos (by norm_num) (r_pos _ (densityY_spec l hl).1))

lemma volume_profile_C_pos (l : ℝ) (hl : 0 ≤ l) : 0 < profileC l := by
  rw [volume_profile_C_physical l hl]
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
    (J_sub_XR_pos_interior _ (densityY_spec l hl).1)

lemma volume_profile_logB_hasDerivAt (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun t => Real.log (volumeProfileBPhysical t))
      (2*(1-deriv T Y)/r Y) Y := by
  have hr := r_pos Y ⟨hY.1.le,hY.2⟩
  have hrad : HasDerivAt r (2*(deriv T Y-1)) Y := by
    have ht := (((T_analyticAt_interior Y ⟨hY.1.le,hY.2⟩).differentiableAt.hasDerivAt).sub
      (hasDerivAt_id Y)).const_mul 2
    have he : r =ᶠ[𝓝 Y] (fun t => 2*(T t-t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hY] with t ht
      have hh := T_eq_firstKernelEndpoint t ⟨ht.1.le,ht.2⟩
      linarith
    exact ht.congr_of_eventuallyEq he
  have hd := ((hasDerivAt_const Y (Real.pi^2)).div
    (hrad.const_mul 2) (mul_pos (by norm_num) hr).ne').log
      (div_pos (sq_pos_of_pos Real.pi_pos) (mul_pos (by norm_num) hr)).ne'
  convert hd using 1
  · rfl
  · dsimp only [Pi.div_apply,Pi.mul_apply]
    field_simp [hr.ne',Real.pi_ne_zero]
    <;> ring

lemma volume_profile_logC_hasDerivAt (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt (fun t => Real.log (volumeProfileCPhysical t))
      ((a Y-deriv J Y)/(J Y-XR Y)) Y := by
  have hD := J_sub_XR_pos_interior Y hY
  have hd := ((hasDerivAt_const Y (2*Real.pi^2)).div
    (((J_analyticAt_interior Y hY).differentiableAt.hasDerivAt).sub (XR_hasDerivAt Y)) hD.ne').log
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)) hD).ne'
  convert hd using 1
  · rfl
  · dsimp only [Pi.div_apply,Pi.mul_apply,Pi.sub_apply]
    field_simp [hD.ne',Real.pi_ne_zero]
    <;> ring

lemma volume_profile_logB_weighted_deriv (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    |2*(1-deriv T Y)/r Y| *(1+density Y) ≤ 4*deriv density Y := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have hr := r_pos Y hYi
  have ht := T_deriv_neg_interior Y hYi
  have hl := T_deriv_lower_interior Y hYi
  have hd := volume_profile_density_jacobian Y hYi
  have hp : 0 < 1+density Y := by linarith [density_nonneg Y hYi]
  have hnon : 0 ≤ 2*(1-deriv T Y) := by linarith
  rw [abs_of_nonneg (div_nonneg hnon hr.le)]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hr).2
  have hmul := mul_le_mul_of_nonneg_right (show 2*(1-deriv T Y) ≤ 4 by linarith) hp.le
  nlinarith

lemma volume_profile_logC_weighted_deriv (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    |(a Y-deriv J Y)/(J Y-XR Y)| *(1+density Y) ≤ deriv density Y := by
  have ha := a_pos Y hY
  have hd := volume_profile_J_deriv_bounds Y hY
  have hD := J_sub_XR_pos_interior Y hY
  have hn : 0 ≤ a Y-deriv J Y := by linarith
  rw [abs_of_nonneg (div_nonneg hn hD.le),
    density_J_formula_on_domain Y (stationaryParameterDomain_contains Y hY),
    (density_hasDerivAt_interior Y hY).deriv]
  have he : (a Y-deriv J Y)/(J Y-XR Y)*(1+2*XR Y/(J Y-XR Y)) =
      ((a Y-deriv J Y)*(J Y+XR Y))/(J Y-XR Y)^2 := by
    field_simp
    <;> ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith [mul_nonneg (show 0 ≤ a Y+deriv J Y by linarith) hD.le]

lemma volume_profile_logB_continuousOn :
    ContinuousOn (fun Y => Real.log (volumeProfileBPhysical Y)) (Ico 0 y₀) := by
  have hr : ContinuousOn r (Ico 0 y₀) :=
    continuousOn_iff_continuous_domRestrict.mpr r_continuous_interior
  apply (continuousOn_const.div (continuousOn_const.mul hr) ?_).log ?_
  · intro Y hY
    exact (mul_pos (by norm_num) (r_pos Y hY)).ne'
  · intro Y hY
    exact (div_pos (sq_pos_of_pos Real.pi_pos) (mul_pos (by norm_num) (r_pos Y hY))).ne'

lemma volume_profile_logC_continuousOn :
    ContinuousOn (fun Y => Real.log (volumeProfileCPhysical Y)) (Ico 0 y₀) := by
  have hJ : ContinuousOn J (Ico 0 y₀) := fun Y hY =>
    (J_analyticAt_interior Y hY).continuousAt.continuousWithinAt
  apply (continuousOn_const.div (hJ.sub XR_continuous.continuousOn) ?_).log ?_
  · intro Y hY
    exact (J_sub_XR_pos_interior Y hY).ne'
  · intro Y hY
    exact (div_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
      (J_sub_XR_pos_interior Y hY)).ne'

/-- Cauchy's mean-value theorem transfers an actual physical-parameter derivative
bound into a uniform density-coordinate logarithmic estimate. -/
lemma volume_profile_weighted_comparison (f f' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ContinuousOn f (Ico 0 y₀))
    (hd : ∀ Y ∈ Ioo 0 y₀, HasDerivAt f (f' Y) Y)
    (hbound : ∀ Y ∈ Ioo 0 y₀,
      |f' Y| * (1+density Y) ≤ C*deriv density Y)
    (Y Z : ℝ) (hY : Y ∈ Ico 0 y₀) (hZ : Z ∈ Ico 0 y₀) (hYZ : Y ≤ Z) :
    |f Z-f Y| ≤ C*(density Z-density Y)/(1+density Y) := by
  by_cases he : Y = Z
  · subst Z
    simp
  have hlt : Y < Z := lt_of_le_of_ne hYZ he
  have hsub : Icc Y Z ⊆ Ico 0 y₀ := fun t ht => ⟨le_trans hY.1 ht.1,lt_of_le_of_lt ht.2 hZ.2⟩
  have hsubo : Ioo Y Z ⊆ Ioo 0 y₀ := fun t ht => ⟨lt_of_le_of_lt hY.1 ht.1,lt_trans ht.2 hZ.2⟩
  have hdc : ContinuousOn density (Icc Y Z) := fun t ht =>
    (density_analyticAt_interior t (hsub ht)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hlt
    (hc.mono hsub) (fun t ht => hd t (hsubo ht)) density (deriv density) hdc
    (fun t ht => (density_analyticAt_interior t (hsub ⟨ht.1.le,ht.2.le⟩)).differentiableAt.hasDerivAt)
  have hti : t ∈ Ico 0 y₀ := ⟨(hsubo ht).1.le,(hsubo ht).2⟩
  have hden : 0 < 1+density Y := by linarith [density_nonneg Y hY]
  have hdp := density_deriv_pos_interior t hti
  have hdiff : 0 ≤ density Z-density Y :=
    sub_nonneg.mpr (density_strictMonoOn.monotoneOn hY hZ hYZ)
  have hmono : density Y ≤ density t := density_strictMonoOn.monotoneOn hY hti ht.1.le
  have hh := hbound t (hsubo ht)
  have ha : |f' t| * (1+density Y) ≤ C*deriv density t := by
    nlinarith [mul_nonneg (abs_nonneg (f' t)) (sub_nonneg.mpr hmono)]
  have heqabs : (density Z-density Y)*|f' t| = |f Z-f Y| *deriv density t := by
    have hh' := congrArg abs heq
    simpa only [abs_mul,abs_of_nonneg hdiff,abs_of_pos hdp] using hh'
  apply (le_div_iff₀ hden).2
  have hp := mul_le_mul_of_nonneg_left ha hdiff
  have hemul := congrArg (fun q : ℝ => q*(1+density Y)) heqabs
  nlinarith [hemul]

lemma volume_profile_density_comparison (F f f' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ContinuousOn f (Ico 0 y₀))
    (hd : ∀ Y ∈ Ioo 0 y₀, HasDerivAt f (f' Y) Y)
    (hbound : ∀ Y ∈ Ioo 0 y₀,
      |f' Y| * (1+density Y) ≤ C*deriv density Y)
    (he : ∀ l : ℝ, 0 ≤ l → F l=f (densityY l))
    (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    |F l-F m| ≤ C*|l-m|/(1+min l m) := by
  have hordered (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) (hlm : l ≤ m) :
      |F l-F m| ≤ C*(m-l)/(1+l) := by
    have hls := densityY_spec l hl
    have hms := densityY_spec m hm
    have hle : densityY l ≤ densityY m := by
      apply (density_strictMonoOn.le_iff_le hls.1 hms.1).mp
      simpa only [hls.2,hms.2] using hlm
    have hh := volume_profile_weighted_comparison f f' C hC hc hd hbound
      _ _ hls.1 hms.1 hle
    rw [←he m hm,←he l hl,hls.2,hms.2] at hh
    simpa only [abs_sub_comm] using hh
  rcases le_total l m with hlm | hml
  · simpa only [min_eq_left hlm,abs_of_nonpos (sub_nonpos.mpr hlm),neg_sub]
      using hordered l m hl hm hlm
  · simpa only [min_eq_right hml,abs_of_nonneg (sub_nonneg.mpr hml),abs_sub_comm]
      using hordered m l hm hl hml

/-- Actual original profile B, including zero and unbounded density. -/
lemma volume_profile_B_log_comparison (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    |Real.log (profileB l)-Real.log (profileB m)| ≤ 4*|l-m|/(1+min l m) := by
  apply volume_profile_density_comparison (fun l => Real.log (profileB l))
    (fun Y => Real.log (volumeProfileBPhysical Y))
    (fun Y => 2*(1-deriv T Y)/r Y) 4 (by norm_num)
    volume_profile_logB_continuousOn volume_profile_logB_hasDerivAt
    volume_profile_logB_weighted_deriv
  · intro l hl
    rw [volume_profile_B_physical l hl]
  · exact hl
  · exact hm

/-- Actual original profile C, with the stated continuous value C(0)=4π². -/
lemma volume_profile_C_log_comparison (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    |Real.log (profileC l)-Real.log (profileC m)| ≤ |l-m|/(1+min l m) := by
  have hh := volume_profile_density_comparison (fun l => Real.log (profileC l))
    (fun Y => Real.log (volumeProfileCPhysical Y))
    (fun Y => (a Y-deriv J Y)/(J Y-XR Y)) 1 (by norm_num)
    volume_profile_logC_continuousOn
    (fun Y hY => volume_profile_logC_hasDerivAt Y ⟨hY.1.le,hY.2⟩)
    (by intro Y hY; simpa only [one_mul] using
      volume_profile_logC_weighted_deriv Y ⟨hY.1.le,hY.2⟩)
    (by intro l hl; rw [volume_profile_C_physical l hl]) l m hl hm
  simpa only [one_mul] using hh

lemma volume_profile_densityY_weighted_difference (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    |densityY l-densityY m| ≤ (Real.pi^2/2)*|l-m|/(1+min l m) := by
  apply volume_profile_density_comparison densityY id (fun _ => 1)
    (Real.pi^2/2) (by positivity) continuousOn_id
    (fun Y _ => hasDerivAt_id Y) ?_ (fun _ _ => rfl) l m hl hm
  intro Y hY
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  simp only [abs_one,one_mul]
  have hd := volume_profile_density_jacobian Y hYi
  have hr : r Y ≤ Real.pi^2/2 := by linarith [r_le_pi Y hYi,hYi.1]
  exact hd.trans (mul_le_mul_of_nonneg_right hr (density_deriv_pos_interior Y hYi).le)

end WP.Analysis
