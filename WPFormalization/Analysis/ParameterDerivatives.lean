import WPFormalization.Analysis.StationaryWeighted
import WPFormalization.Analysis.StationaryAnalytic
import WPFormalization.Analysis.ParameterZeroValues

/-! The derivatives of the actual infimum-defined stationary parameter.
The open implicit domain permits genuine differentiation at Y=0. Exact
kernel values give T′(0)=-1; positive T″ then gives the full lower bound. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma T_deriv_stationary_equation_on_domain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    stationaryWeighted (fun s => s^2) (deriv (deriv X)) Y (WP.T Y)+
      deriv WP.T Y*stationaryWeighted (fun s => 1-s^2) (deriv (deriv X)) Y (WP.T Y) = 0 := by
  have hb : HasDerivAt WP.T (deriv WP.T Y) Y :=
    (T_analyticAt_on_stationaryParameterDomain Y hY).differentiableAt.hasDerivAt
  have hd := stationaryWeighted_hasDerivAt_comp (fun _ => 1) continuous_const
    (deriv X) X_differentiable.deriv WP.T Y (deriv WP.T Y) hb
  have heq : (fun x => stationaryWeighted (fun _ => 1) (deriv X) x (WP.T x)) =ᶠ[𝓝 Y] fun _ => 0 := by
    filter_upwards [stationaryParameterDomain_isOpen.mem_nhds hY] with x hx
    rw [stationaryWeighted_one_derivX]
    exact (T_root_on_stationaryParameterDomain x hx).2
  have hz := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const Y (0 : ℝ))
  simp only [one_mul] at hz
  have hg : Continuous (deriv (deriv X)) := X_differentiable.deriv.deriv.continuous
  have ha := stationaryWeighted_add (fun s : ℝ => s^2)
    (fun s => deriv WP.T Y*(1-s^2)) (by fun_prop) (by fun_prop) (deriv (deriv X)) hg Y (WP.T Y)
  have hb' := stationaryWeighted_smul (deriv WP.T Y) (fun s : ℝ => 1-s^2)
    (by fun_prop) (deriv (deriv X)) hg Y (WP.T Y)
  rw [ha,hb'] at hz
  exact hz
lemma stationary_second_weighted_neg (q : ℝ → ℝ) (hq : Continuous q)
    (Y T : ℝ) (hYT : Y ≤ T) (hT : T ≤ (5/2 : ℝ))
    (hn : ∀ s ∈ Icc (0 : ℝ) 1,0 ≤ q s) (hp : ∃ s ∈ Icc (0 : ℝ) 1,0 < q s) :
    stationaryWeighted q (deriv (deriv X)) Y T < 0 := by
  have hg : Continuous (deriv (deriv X)) := X_differentiable.deriv.deriv.continuous
  rw [stationaryWeighted_real_integral q hq _ hg]
  have harg (s : ℝ) : T-(T-Y)*s^2 ≤ (5/2 : ℝ) := by
    have hh := mul_nonneg (sub_nonneg.mpr hYT) (sq_nonneg s)
    linarith
  have hneg (s : ℝ) : (deriv (deriv X) ((T-(T-Y)*s^2 : ℝ) : ℂ)).re < 0 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using
      second_X_neg_before _ (harg s)
  have hc : Continuous (fun s : ℝ => q s*(deriv (deriv X) ((T-(T-Y)*s^2 : ℝ) : ℂ)).re) := by fun_prop
  obtain ⟨s,hs,hps⟩ := hp
  have he := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    zero_lt_one hc.continuousOn continuous_const.continuousOn
    (g := fun _ : ℝ => (0 : ℝ)) (fun s hs =>
      mul_nonpos_of_nonneg_of_nonpos (hn s ⟨hs.1.le,hs.2⟩) (hneg s).le)
    ⟨s,hs,mul_neg_of_pos_of_neg hps (hneg s)⟩
  simpa only [intervalIntegral.integral_zero] using he
lemma T_deriv_neg_on_domain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) : deriv WP.T Y < 0 := by
  have hs := T_root_on_stationaryParameterDomain Y hY
  have hYT : Y ≤ WP.T Y := le_trans hY.1.le hs.1.1.le
  have hA := stationary_second_weighted_neg (fun s : ℝ => s^2) (by fun_prop)
    Y (WP.T Y) hYT hs.1.2.le (fun s hs => sq_nonneg s) ⟨1,by norm_num,by norm_num⟩
  have hB := stationary_second_weighted_neg (fun s : ℝ => 1-s^2) (by fun_prop)
    Y (WP.T Y) hYT hs.1.2.le (fun s hs => by nlinarith [hs.1,hs.2]) ⟨0,by norm_num,by norm_num⟩
  have he := T_deriv_stationary_equation_on_domain Y hY
  by_contra h
  have hd : 0 ≤ deriv WP.T Y := le_of_not_gt h
  have hm := mul_nonpos_of_nonneg_of_nonpos hd hB.le
  linarith
lemma T_deriv_neg_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : deriv WP.T Y < 0 :=
  T_deriv_neg_on_domain Y (stationaryParameterDomain_contains Y hY)
lemma T_second_deriv_stationary_equation_on_domain (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    stationaryWeighted (fun s => (s^2+deriv WP.T Y*(1-s^2))^2)
        (deriv (deriv (deriv X))) Y (WP.T Y)+
      iteratedDeriv 2 WP.T Y*stationaryWeighted (fun s => 1-s^2) (deriv (deriv X)) Y (WP.T Y) = 0 := by
  have hb : HasDerivAt WP.T (deriv WP.T Y) Y :=
    (T_analyticAt_on_stationaryParameterDomain Y hY).differentiableAt.hasDerivAt
  have hb₂ : HasDerivAt (deriv WP.T) (iteratedDeriv 2 WP.T Y) Y := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using
      (T_analyticAt_on_stationaryParameterDomain Y hY).deriv.differentiableAt.hasDerivAt
  have hg : Differentiable ℂ (deriv (deriv X)) := X_differentiable.deriv.deriv
  have hA := stationaryWeighted_hasDerivAt_comp (fun s : ℝ => s^2) (by fun_prop)
    (deriv (deriv X)) hg WP.T Y (deriv WP.T Y) hb
  have hB := stationaryWeighted_hasDerivAt_comp (fun s : ℝ => 1-s^2) (by fun_prop)
    (deriv (deriv X)) hg WP.T Y (deriv WP.T Y) hb
  have hd := hA.add (hb₂.mul hB)
  have heq : (fun x => stationaryWeighted (fun s => s^2) (deriv (deriv X)) x (WP.T x)+
      deriv WP.T x*stationaryWeighted (fun s => 1-s^2) (deriv (deriv X)) x (WP.T x)) =ᶠ[𝓝 Y] fun _ => 0 := by
    filter_upwards [stationaryParameterDomain_isOpen.mem_nhds hY] with x hx
    exact T_deriv_stationary_equation_on_domain x hx
  have hz := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const Y (0 : ℝ))
  have hc : Continuous (deriv (deriv (deriv X))) := hg.deriv.continuous
  have hsq : stationaryWeighted (fun s => (s^2+deriv WP.T Y*(1-s^2))^2)
        (deriv (deriv (deriv X))) Y (WP.T Y) =
      stationaryWeighted (fun s => s^2*(s^2+deriv WP.T Y*(1-s^2)))
        (deriv (deriv (deriv X))) Y (WP.T Y)+
      deriv WP.T Y*stationaryWeighted (fun s => (1-s^2)*(s^2+deriv WP.T Y*(1-s^2)))
        (deriv (deriv (deriv X))) Y (WP.T Y) := by
    have he : (fun s : ℝ => (s^2+deriv WP.T Y*(1-s^2))^2) =
        (fun s => s^2*(s^2+deriv WP.T Y*(1-s^2))+
          deriv WP.T Y*((1-s^2)*(s^2+deriv WP.T Y*(1-s^2)))) := by funext s; ring
    rw [he,stationaryWeighted_add
      (fun s : ℝ => s^2*(s^2+deriv WP.T Y*(1-s^2)))
      (fun s => deriv WP.T Y*((1-s^2)*(s^2+deriv WP.T Y*(1-s^2))))
      (by fun_prop) (by fun_prop) _ hc,
      stationaryWeighted_smul (deriv WP.T Y)
        (fun s : ℝ => (1-s^2)*(s^2+deriv WP.T Y*(1-s^2))) (by fun_prop) _ hc]
  linarith
lemma stationary_third_weighted_pos (q : ℝ → ℝ) (hq : Continuous q)
    (Y T : ℝ) (hY : 0 ≤ Y) (hYT : Y ≤ T) (hT : T ≤ Real.pi^2/4)
    (hn : ∀ s ∈ Icc (0 : ℝ) 1,0 ≤ q s) (hp : ∃ s ∈ Icc (0 : ℝ) 1,0 < q s) :
    0 < stationaryWeighted q (deriv (deriv (deriv X))) Y T := by
  have hg : Continuous (deriv (deriv (deriv X))) := X_differentiable.deriv.deriv.deriv.continuous
  rw [stationaryWeighted_real_integral q hq _ hg]
  have harg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : T-(T-Y)*s^2 ∈ Icc 0 (Real.pi^2/4) := by
    have hs2 : s^2 ≤ 1 := by nlinarith [hs.1,hs.2]
    have hlow := mul_nonneg (sub_nonneg.mpr hYT) (sub_nonneg.mpr hs2)
    have hupp := mul_nonneg (sub_nonneg.mpr hYT) (sq_nonneg s)
    constructor <;> nlinarith
  have hpos (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      0 < (deriv (deriv (deriv X)) ((T-(T-Y)*s^2 : ℝ) : ℂ)).re := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using
      (bessel_signs_pi_interval.2.1 _ (harg s hs)).2
  have hc : Continuous (fun s : ℝ => q s*(deriv (deriv (deriv X)) ((T-(T-Y)*s^2 : ℝ) : ℂ)).re) := by fun_prop
  apply intervalIntegral.integral_pos zero_lt_one hc.continuousOn
  · intro s hs
    exact mul_nonneg (hn s ⟨hs.1.le,hs.2⟩) (hpos s ⟨hs.1.le,hs.2⟩).le
  · obtain ⟨s,hs,hqs⟩ := hp
    exact ⟨s,hs,mul_pos hqs (hpos s hs)⟩
lemma T_second_deriv_pos_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < iteratedDeriv 2 WP.T Y := by
  have hD := stationaryParameterDomain_contains Y hY
  have hs := WP.stationary_root_proof Y hY
  have hYT : Y ≤ WP.T Y := le_trans hY.2.le hs.1.1.le
  have hT : WP.T Y ≤ (5/2 : ℝ) := by
    have hp : Real.pi^2/4 < (5/2 : ℝ) := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
    exact le_trans hs.1.2 hp.le
  have hB := stationary_second_weighted_neg (fun s : ℝ => 1-s^2) (by fun_prop)
    Y (WP.T Y) hYT hT (fun s hs => by nlinarith [hs.1,hs.2]) ⟨0,by norm_num,by norm_num⟩
  have hC := stationary_third_weighted_pos (fun s : ℝ => (s^2+deriv WP.T Y*(1-s^2))^2)
    (by fun_prop) Y (WP.T Y) hY.1 hYT hs.1.2 (fun s hs => sq_nonneg _) ⟨1,by norm_num,by norm_num⟩
  have he := T_second_deriv_stationary_equation_on_domain Y hD
  by_contra h
  have hd : iteratedDeriv 2 WP.T Y ≤ 0 := le_of_not_gt h
  have hm := mul_nonneg_of_nonpos_of_nonpos hd hB.le
  linarith
lemma stationaryWeighted_kernel_path (q : ℝ → ℝ) (g : ℂ → ℂ) (Y T : ℝ) :
    stationaryWeighted q g Y T =
      (∫ s : ℝ in (0)..1,(q s : ℂ)*g ((Y:ℂ)+((2*(T-Y):ℝ):ℂ)/2*(1-(s:ℂ)^2))).re := by
  unfold stationaryWeighted
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have he : stationaryQLinear s ((Y:ℂ),(T:ℂ)) =
      (Y:ℂ)+((2*(T-Y):ℝ):ℂ)/2*(1-(s:ℂ)^2) := by
    change (s:ℂ)^2*(Y:ℂ)+(1-(s:ℂ)^2)*(T:ℂ) = _
    push_cast
    ring
  dsimp only
  rw [he]
lemma stationary_second_moment_identity (Y T : ℝ) :
    stationaryQReal Y T-2*(T-Y)*stationaryWeighted (fun s => s^2) (deriv (deriv X)) Y T = a Y := by
  have he := congrArg Complex.re
    (kernelIntegral_first_moment (deriv X) X_differentiable.deriv (Y:ℂ) ((2*(T-Y):ℝ):ℂ))
  rw [stationaryWeighted_kernel_path]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at he
  simpa only [stationaryQReal,stationaryQ_eq_K,K,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_ofNat,a] using he
lemma stationary_second_moment_T (Y T : ℝ) :
    stationaryWeighted (fun s => 1-s^2) (deriv (deriv X)) Y T =
      2*(deriv (K Y) ((2*(T-Y):ℝ):ℂ)).re := by
  rw [stationaryWeighted_kernel_path,K_deriv_integral]
  have hc : (∫ s : ℝ in (0)..1,((1-s^2:ℝ):ℂ)*deriv (deriv X)
      ((Y:ℂ)+((2*(T-Y):ℝ):ℂ)/2*(1-(s:ℂ)^2))) =
      2*(∫ s : ℝ in (0)..1,((1-(s:ℂ)^2)/2)*deriv (deriv X)
      ((Y:ℂ)+((2*(T-Y):ℝ):ℂ)/2*(1-(s:ℂ)^2))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    push_cast
    ring
  rw [hc]
  norm_num [Complex.mul_re]
lemma T_deriv_zero_value : deriv WP.T 0 = -1 := by
  have h0 : (0:ℝ) ∈ Ico 0 y₀ := ⟨le_rfl,y₀_pos⟩
  have hD := stationaryParameterDomain_contains 0 h0
  have hQ := (T_root_on_stationaryParameterDomain 0 hD).2
  have hA := stationary_second_moment_identity 0 (WP.T 0)
  have hB := stationary_second_moment_T 0 (WP.T 0)
  have hH := WP.H_zero_pi_value
  rw [WP.H_zero_eq_K_deriv] at hH
  have hhre := congrArg Complex.re hH
  have hp : Real.pi^2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hK : (deriv (K 0) ((Real.pi^2/2:ℝ):ℂ)).re = -1/Real.pi^2 := by
    have hc : (3/(Real.pi:ℂ)^2).re = 3/Real.pi^2 := by
      rw [← Complex.ofReal_pow,← Complex.ofReal_ofNat 3,← Complex.ofReal_div,Complex.ofReal_re]
    rw [hc] at hhre
    norm_num [Complex.mul_re] at hhre
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat] at hhre ⊢
    linear_combination -(1/3:ℝ)*hhre
  have hs : 2*(WP.T 0-0) = Real.pi^2/2 := by rw [WP.T_zero_value]; ring
  rw [hQ,WP.a_zero,WP.T_zero_value] at hA
  simp only [Complex.ofReal_zero] at hB
  rw [hs,hK] at hB
  have he := T_deriv_stationary_equation_on_domain 0 hD
  rw [hB] at he
  have hden : Real.pi^2 > 0 := sq_pos_of_pos Real.pi_pos
  have ha : stationaryWeighted (fun s => s^2) (deriv (deriv X)) 0 (WP.T 0) = -2/Real.pi^2 := by
    rw [WP.T_zero_value]
    apply (eq_div_iff hp).mpr
    nlinarith [hA]
  rw [ha] at he
  field_simp [hp] at he
  linarith
lemma T_deriv_strictMonoOn : StrictMonoOn (deriv WP.T) (Ico 0 y₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 y₀)
  · intro x hx
    exact (T_analyticAt_interior x hx).deriv.continuousAt.continuousWithinAt
  · intro x hx
    have hp := T_second_deriv_pos_interior x (interior_subset hx)
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using hp
lemma T_deriv_lower_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : -1 ≤ deriv WP.T Y := by
  rw [← T_deriv_zero_value]
  exact T_deriv_strictMonoOn.monotoneOn ⟨le_rfl,y₀_pos⟩ hY hY.1
lemma stationaryWeighted_one_X (Y : ℝ) : stationaryWeighted (fun _ => 1) X Y (WP.T Y) = WP.J Y := by
  rw [stationaryWeighted_real_integral _ continuous_const X X_differentiable.continuous]
  simp only [WP.J,WP.Delta,WP.XR,one_mul]
lemma J_hasDerivAt_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt WP.J ((1-deriv WP.T Y)*stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y)) Y := by
  have hd := stationaryWeighted_hasDerivAt_comp (fun _ => 1) continuous_const X X_differentiable
    WP.T Y (deriv WP.T Y) (T_analyticAt_interior Y hY).differentiableAt.hasDerivAt
  have he : (fun x => stationaryWeighted (fun _ => 1) X x (WP.T x)) = WP.J := by
    funext x
    exact stationaryWeighted_one_X x
  rw [he] at hd
  have hw : (fun s : ℝ => 1*(s^2+deriv WP.T Y*(1-s^2))) =
      (fun s => deriv WP.T Y*1+(1-deriv WP.T Y)*s^2) := by funext s; ring
  rw [hw,stationaryWeighted_add (fun _ : ℝ => deriv WP.T Y*1)
    (fun s : ℝ => (1-deriv WP.T Y)*s^2) (by fun_prop) (by fun_prop)
    (deriv X) X_differentiable.deriv.continuous,
    stationaryWeighted_smul (deriv WP.T Y) (fun _ => 1) continuous_const _ X_differentiable.deriv.continuous,
    stationaryWeighted_smul (1-deriv WP.T Y) (fun s : ℝ => s^2) (by fun_prop) _ X_differentiable.deriv.continuous,
    stationaryWeighted_one_derivX] at hd
  have hr := (T_root_on_stationaryParameterDomain Y (stationaryParameterDomain_contains Y hY)).2
  simpa only [hr,mul_zero,zero_add] using hd
lemma J_deriv_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    deriv WP.J Y = (1-deriv WP.T Y)*stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) :=
  (J_hasDerivAt_interior Y hY).deriv
lemma stationary_first_moment_le (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) ≤ a Y/3 := by
  rw [stationaryWeighted_real_integral _ (by fun_prop) _ X_differentiable.deriv.continuous]
  have hs := WP.stationary_root_proof Y hY
  have hYT : Y ≤ WP.T Y := le_trans hY.2.le hs.1.1.le
  have hp : y₀ < Real.pi^2/4 := by nlinarith [y₀_lt_three_halves,Real.pi_gt_three]
  have hg : Continuous (deriv X) := X_differentiable.deriv.continuous
  have hc : Continuous (fun s : ℝ => s^2*(deriv X ((WP.T Y-(WP.T Y-Y)*s^2 : ℝ):ℂ)).re) := by fun_prop
  have hc' : Continuous (fun s : ℝ => s^2*a Y) := by fun_prop
  have hpoint : ∀ s ∈ Icc (0:ℝ) 1,
      s^2*(deriv X ((WP.T Y-(WP.T Y-Y)*s^2:ℝ):ℂ)).re ≤ s^2*a Y := by
    intro s hs'
    have hs2 : s^2 ≤ 1 := by nlinarith [hs'.1,hs'.2]
    have harg : WP.T Y-(WP.T Y-Y)*s^2 ∈ Icc Y (WP.T Y) := by
      have h1 := mul_nonneg (sub_nonneg.mpr hYT) (sub_nonneg.mpr hs2)
      have h2 := mul_nonneg (sub_nonneg.mpr hYT) (sq_nonneg s)
      constructor <;> nlinarith
    have ha := WP.a_strictAntiOn_pi.antitoneOn ⟨hY.1,le_trans hY.2.le hp.le⟩
      ⟨le_trans hY.1 harg.1,le_trans harg.2 hs.1.2⟩ harg.1
    exact mul_le_mul_of_nonneg_left ha (sq_nonneg s)
  have hle := intervalIntegral.integral_mono_on (μ := volume) zero_le_one (hc.intervalIntegrable 0 1)
    (hc'.intervalIntegrable 0 1) hpoint
  have he : (∫ s : ℝ in (0)..1,s^2*a Y) = a Y/3 := by
    rw [intervalIntegral.integral_mul_const]
    norm_num
    ring
  exact le_trans hle he.le

end WP.Analysis
