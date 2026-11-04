import WPFormalization.Analysis.ParameterAnalytic

/-! Complete proof of the original Lemma3.1(i)--(ii) specification. The
critical density divergence follows from the actual J integral and its
positive difference from X; the origin error follows from analyticity. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma J_deriv_upper_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : deriv WP.J Y ≤ 2*a Y/3 := by
  rw [J_deriv_interior Y hY]
  have hT := T_deriv_neg_interior Y hY
  have hl := T_deriv_lower_interior Y hY
  have ha := WP.a_pos Y hY
  have hm := mul_le_mul_of_nonneg_left (stationary_first_moment_le Y hY)
    (by linarith : 0 ≤ 1-deriv WP.T Y)
  nlinarith
lemma beta_hasDerivAt_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt WP.beta ((a Y*WP.J Y-XR Y*deriv WP.J Y)/(WP.J Y)^2) Y := by
  exact (XR_hasDerivAt Y).div (J_analyticAt_interior Y hY).differentiableAt.hasDerivAt (WP.J_pos Y hY).ne'
lemma parameter_ratio_deriv_numerator_pos (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    0 < a Y*WP.J Y-XR Y*deriv WP.J Y := by
  have ha := WP.a_pos Y hY
  have hx := WP.XR_nonneg_interior Y hY
  have hJ := J_sub_XR_pos_interior Y hY
  have hd := mul_le_mul_of_nonneg_left (J_deriv_upper_interior Y hY) hx
  have hp := mul_pos ha hJ
  have hn := mul_nonneg ha.le hx
  nlinarith
lemma beta_deriv_pos_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < deriv WP.beta Y := by
  rw [(beta_hasDerivAt_interior Y hY).deriv]
  exact div_pos (parameter_ratio_deriv_numerator_pos Y hY) (sq_pos_of_pos (WP.J_pos Y hY))
lemma density_hasDerivAt_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt WP.density (2*(a Y*WP.J Y-XR Y*deriv WP.J Y)/(WP.J Y-XR Y)^2) Y := by
  have hJ : HasDerivAt WP.J (deriv WP.J Y) Y := (J_analyticAt_interior Y hY).differentiableAt.hasDerivAt
  have hd := ((XR_hasDerivAt Y).const_mul 2).div (hJ.sub (XR_hasDerivAt Y))
    (J_sub_XR_pos_interior Y hY).ne'
  have heq : (fun x : ℝ => 2*XR x/(WP.J x-XR x)) =ᶠ[𝓝 Y] WP.density := by
    filter_upwards [stationaryParameterDomain_isOpen.mem_nhds (stationaryParameterDomain_contains Y hY)] with x hx
    exact (density_J_formula_on_domain x hx).symm
  simp only [Pi.sub_apply,Pi.div_apply] at hd
  convert hd.congr_of_eventuallyEq heq.symm using 1 <;> ring
lemma density_deriv_pos_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < deriv WP.density Y := by
  rw [(density_hasDerivAt_interior Y hY).deriv]
  exact div_pos (mul_pos (by norm_num) (parameter_ratio_deriv_numerator_pos Y hY))
    (sq_pos_of_pos (J_sub_XR_pos_interior Y hY))
lemma density_strictMonoOn : StrictMonoOn WP.density (Ico 0 y₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 y₀)
  · intro x hx
    exact (density_analyticAt_interior x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact density_deriv_pos_interior x (interior_subset hx)
lemma J_tendsto_critical : Tendsto WP.J (𝓝[<] y₀) (𝓝 xCritical) := by
  let H (p : ComplexPair) : ℂ := ∫ s : ℝ in (0)..1,X (stationaryQLinear s p)
  have hc : Continuous H := by
    apply ContDiff.continuous (𝕜 := ℂ) (n := 1)
    simpa only [H,zero_add,one_mul] using
      affineIntegral_prod_contDiff_one (fun _ => 1) (fun _ => 0) stationaryQLinear
        continuous_const continuous_const stationaryQLinear_continuous X X_differentiable
  have he : (fun Y : ℝ => (H ((Y:ℂ),(WP.T Y:ℂ))).re) = WP.J := by
    funext Y
    simpa only [H,stationaryWeighted,Complex.ofReal_one,one_mul] using stationaryWeighted_one_X Y
  have hp : Tendsto (fun Y : ℝ => ((Y:ℂ),(WP.T Y:ℂ))) (𝓝[<] y₀) (𝓝 ((y₀:ℂ),(y₀:ℂ))) :=
    by
      simpa only [← nhds_prod_eq,Function.comp_def] using
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).prodMk
          (Complex.continuous_ofReal.continuousAt.tendsto.comp WP.T_tendsto_critical)
  have ht := ((Complex.continuous_re.comp hc).continuousAt.tendsto).comp hp
  have hval : (H ((y₀:ℂ),(y₀:ℂ))).re = xCritical := by
    have he' : H ((y₀:ℂ),(y₀:ℂ)) = X y₀ := by
      dsimp [H]
      have heq : (fun s : ℝ => X (stationaryQLinear s ((y₀:ℂ),(y₀:ℂ)))) = fun _ => X (y₀:ℂ) := by
        funext s
        congr 1
        change (s:ℂ)^2*(y₀:ℂ)+(1-(s:ℂ)^2)*(y₀:ℂ) = _
        ring
      rw [heq]
      simp only [intervalIntegral.integral_const,sub_zero,one_smul]
    rw [he']
    rfl
  change Tendsto (fun Y : ℝ => (H ((Y:ℂ),(WP.T Y:ℂ))).re) _
    (𝓝 ((H ((y₀:ℂ),(y₀:ℂ))).re)) at ht
  rwa [he,hval] at ht
lemma density_tendsto_atTop_critical : Tendsto WP.density (𝓝[<] y₀) atTop := by
  have hx : Tendsto XR (𝓝[<] y₀) (𝓝 xCritical) :=
    (XR_analyticAt y₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hm : ∀ᶠ Y in 𝓝[<] y₀,Y ∈ Ico 0 y₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    exact ⟨hpos.le,hY⟩
  have hd : Tendsto (fun Y => WP.J Y-XR Y) (𝓝[<] y₀) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using J_tendsto_critical.sub hx
    · filter_upwards [hm] with Y hY
      exact J_sub_XR_pos_interior Y hY
  have hn : Tendsto (fun Y => 2*XR Y) (𝓝[<] y₀) (𝓝 (2*xCritical)) := tendsto_const_nhds.mul hx
  have hpos : 0 < xCritical := by
    have hp : y₀ < Real.pi^2/4 := by nlinarith [y₀_lt_three_halves,Real.pi_gt_three]
    exact (bessel_signs_pi_interval.1 y₀ ⟨y₀_pos,hp.le⟩)
  have ht := hn.pos_mul_atTop (by positivity : 0 < 2*xCritical) hd.inv_tendsto_nhdsGT_zero
  have he : (fun Y => 2*XR Y*(WP.J Y-XR Y)⁻¹) =ᶠ[𝓝[<] y₀] WP.density := by
    filter_upwards [hm] with Y hY
    simpa only [div_eq_mul_inv] using (density_J_formula_on_domain Y (stationaryParameterDomain_contains Y hY)).symm
  exact ht.congr' he
lemma density_bijOn : BijOn WP.density (Ico 0 y₀) (Ici 0) := by
  refine ⟨fun Y hY => WP.density_nonneg Y hY,density_strictMonoOn.injOn,?_⟩
  intro l hl
  have hmem : 𝓝[<] y₀ ≤ 𝓟 (Ico 0 y₀) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hY hpos
    exact ⟨hpos.le,hY⟩
  have hc : ContinuousOn WP.density (Ico 0 y₀) := fun Y hY =>
    (density_analyticAt_interior Y hY).continuousAt.continuousWithinAt
  have he := isPreconnected_Ico.intermediate_value₂_eventually₁
    (f := WP.density) (g := fun _ : ℝ => l) (a := 0) ⟨le_rfl,y₀_pos⟩ hmem hc continuousOn_const
    (by simpa only [WP.density_zero_value,Set.mem_Ici] using hl)
    (density_tendsto_atTop_critical.eventually_ge_atTop l)
  obtain ⟨Y,hY,hv⟩ := he
  exact ⟨Y,hY,hv⟩
lemma density_deriv_zero_value : deriv WP.density 0 = 4 := by
  rw [(density_hasDerivAt_interior 0 ⟨le_rfl,y₀_pos⟩).deriv]
  have hx : XR 0 = 0 := by simp [XR,X]
  rw [WP.a_zero,WP.J_zero_value,hx]
  norm_num
lemma analytic_first_order_error_at_zero (f : ℝ → ℝ) (ha : AnalyticAt ℝ f 0) :
    (fun Y => f Y-f 0-deriv f 0*Y) =O[𝓝 0] (fun Y => Y^2) := by
  obtain ⟨p,hp⟩ := ha
  have he (Y : ℝ) : p.partialSum 2 Y = f 0+deriv f 0*Y := by
    have h0 := hp.coeff_zero (fun _ => Y)
    have h1 : p 1 (fun _ => Y) = Y*(p 1 (fun _ => 1)) := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one,smul_eq_mul,mul_one]
        using (p 1).map_smul_univ (fun _ : Fin 1 => Y) (fun _ => (1:ℝ))
    rw [FormalMultilinearSeries.partialSum]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,h0,h1,← hp.deriv]
    ring
  have ht := hp.isBigO_sub_partialSum_pow 2
  simpa only [zero_add,he,sub_add_eq_sub_sub,mul_comm,Real.norm_eq_abs,sq_abs] using ht
lemma density_origin_error : (fun Y => WP.density Y-4*Y) =O[𝓝[>] (0:ℝ)] (fun Y => Y^2) := by
  have he := analytic_first_order_error_at_zero WP.density
    (density_analyticAt_interior 0 ⟨le_rfl,y₀_pos⟩)
  simpa only [WP.density_zero_value,density_deriv_zero_value,sub_zero] using
    he.mono nhdsWithin_le_nhds
theorem parameter_regular_proof :
    (∀ Y ∈ Set.Ico 0 y₀,
      AnalyticAt ℝ T Y ∧ -1 ≤ deriv T Y ∧ deriv T Y < 0 ∧
      0 < iteratedDeriv 2 T Y ∧ 0 < action Y ∧
      J Y = XR Y + action Y / Real.sqrt (Delta Y) ∧
      beta Y = density Y / (2+density Y) ∧ 0 < deriv beta Y ∧ AnalyticAt ℝ density Y) ∧
    StrictMonoOn density (Set.Ico 0 y₀) ∧
    Set.BijOn density (Set.Ico 0 y₀) (Set.Ici 0) ∧
    T 0 = Real.pi^2/4 ∧ action 0 = Real.pi/4 ∧ J 0 = 1/2 ∧
    Tendsto T (𝓝[<] y₀) (𝓝 y₀) ∧
    (fun Y => density Y - 4*Y) =O[𝓝[>] (0 : ℝ)] (fun Y => Y^2) := by
  refine ⟨?_,density_strictMonoOn,density_bijOn,WP.T_zero_value,WP.action_zero_value,
    WP.J_zero_value,WP.T_tendsto_critical,density_origin_error⟩
  intro Y hY
  exact ⟨T_analyticAt_interior Y hY,T_deriv_lower_interior Y hY,T_deriv_neg_interior Y hY,
    T_second_deriv_pos_interior Y hY,WP.action_pos Y hY,WP.J_action_identity Y hY,
    WP.beta_density_identity Y hY,beta_deriv_pos_interior Y hY,density_analyticAt_interior Y hY⟩

end WP.Analysis
