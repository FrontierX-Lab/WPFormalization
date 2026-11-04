import WPFormalization.Coefficients.SaddleActionRegularity
/-! The actual saddle chi is uniformly positive and Lipschitz on [0,3/2].
The original logarithmic degree profile has derivative -log(4 alpha chi),
and its finite secants have a quantitative quadratic remainder.
All statements use the original infimum saddle and original profile. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology

def saddleChi (u : ℝ) : ℝ := (kernelLogSlope (saddleZeta u : ℂ)).re

def adjacentProfileQ (α : ℝ) : ℝ := 4 * α * saddleChi ((3-α)/2)

lemma saddleZeta_abs_lipschitz (u v : ℝ) (hu : u∈Icc (0:ℝ) (3/2))
    (hv : v∈Icc (0:ℝ) (3/2)) :
    |saddleZeta v-saddleZeta u| ≤ 5*|v-u| := by
  rcases le_total u v with huv | hvu
  · have he := saddleZeta_ordered_lipschitz u v hu hv huv
    simpa only [abs_of_nonneg he.1, abs_of_nonneg (sub_nonneg.mpr huv)] using he.2
  · have he := saddleZeta_ordered_lipschitz v u hv hu hvu
    rw [abs_sub_comm, abs_sub_comm v u]
    simpa only [abs_of_nonneg he.1, abs_of_nonneg (sub_nonneg.mpr hvu)] using he.2

lemma saddleZeta_lipschitzOn : LipschitzOnWith 5 saddleZeta (Icc (0:ℝ) (3/2)) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro u hu v hv
  simpa only [Real.dist_eq, NNReal.coe_ofNat] using (saddleZeta_abs_lipschitz v u hv hu)

lemma saddleChi_zero : saddleChi 0=1/5 := by
  simp only [saddleChi,saddleZeta_zero,Complex.ofReal_zero,kernelLogSlope_zero]
  norm_num

lemma saddleChi_lower (u : ℝ) (hu : u∈Icc (0:ℝ) (3/2)) : 1/5 ≤ saddleChi u := by
  have hz := saddleZeta_spec u hu
  by_cases hzero : saddleZeta u=0
  · simp only [saddleChi,hzero,Complex.ofReal_zero,kernelLogSlope_zero]
    norm_num
  · have hp : 0<saddleZeta u := lt_of_le_of_ne hz.1.1 (Ne.symm hzero)
    have hh := unscaledMean_lower_linear (saddleZeta u) hz.1
    rw [unscaledMean_eq_logSlope] at hh
    change _ ≤ saddleZeta u * saddleChi u at hh
    nlinarith only [hh,hp]

lemma saddleChi_mul_saddleZeta (u : ℝ) (hu : u∈Icc (0:ℝ) (3/2)) :
    saddleZeta u * saddleChi u = u := by
  change saddleZeta u * (kernelLogSlope (saddleZeta u:ℂ)).re = u
  rw [←unscaledMean_eq_logSlope]
  exact (saddleZeta_spec u hu).2

lemma saddleChi_uniform_lipschitz : ∃C:ℝ,0<C ∧
    ∀u∈Icc (0:ℝ) (3/2), ∀v∈Icc (0:ℝ) (3/2),
      |saddleChi v-saddleChi u| ≤ C*|v-u| := by
  obtain ⟨R,hR,hzero⟩ := unscaled_kernel_zero_free_radius
  have hAn (z:ℝ) (hz:z∈Icc (0:ℝ) (r 0)) : AnalyticAt ℂ kernelLogSlope (z:ℂ) := by
    apply kernelLogSlope_analyticAt R (fun w hw=>hzero w hw.le)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1]
    exact hz.2.trans_lt hR
  let F : ℝ→ℝ := fun z=>(kernelLogSlope (z:ℂ)).re
  let F' : ℝ→ℝ := fun z=>(deriv kernelLogSlope (z:ℂ)).re
  have hd (z:ℝ) (hz:z∈Icc (0:ℝ) (r 0)) : HasDerivAt F (F' z) z := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt z
      (hAn z hz).differentiableAt.hasDerivAt.comp_ofReal
  have hc : ContinuousOn (fun z=>|F' z|) (Icc (0:ℝ) (r 0)) := by
    intro z hz
    exact (Complex.continuous_re.continuousAt.comp
      ((hAn z hz).deriv.continuousAt.comp Complex.continuous_ofReal.continuousAt)).abs.continuousWithinAt
  obtain ⟨zm,hzm,hm⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0,le_rfl,(r_pos 0 ⟨le_rfl,y₀_pos⟩).le⟩ hc
  let C : ℝ := |F' zm|+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨5*C,by positivity,?_⟩
  intro u hu v hv
  have hzu := (saddleZeta_spec u hu).1
  have hzv := (saddleZeta_spec v hv).1
  have he := (convex_Icc (0:ℝ) (r 0)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz=>(hd z hz).hasDerivWithinAt)
    (fun z hz=>show ‖F' z‖≤C by rw [Real.norm_eq_abs];exact (hm hz).trans (by dsimp[C];linarith)) hzu hzv
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at he
  change |saddleChi v-saddleChi u| ≤ _ at he
  calc _ ≤ C*|saddleZeta v-saddleZeta u| := he
       _ ≤ C*(5*|v-u|) := mul_le_mul_of_nonneg_left (saddleZeta_abs_lipschitz u v hu hv) hC.le
       _ = _ := by ring

lemma saddleZeta_hasDerivAt (u : ℝ) (hu:u∈Ioo (0:ℝ) (3/2)) :
    HasDerivAt saddleZeta (deriv unscaledMean (saddleZeta u))⁻¹ u := by
  have hcont : ContinuousAt saddleZeta u :=
    saddleZeta_lipschitzOn.continuousOn.continuousAt (Icc_mem_nhds hu.1 hu.2)
  have hz := (saddleZeta_spec u ⟨hu.1.le,hu.2.le⟩).1
  exact HasDerivAt.of_local_left_inverse hcont
    ((unscaledMean_hasDerivAt _ hz).differentiableAt.hasDerivAt)
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/5) (unscaledMean_deriv_lower _ hz)))
    (by filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
        exact (saddleZeta_spec v ⟨hv.1.le,hv.2.le⟩).2)

lemma saddleChi_log_lipschitz : ∃C:ℝ,0<C ∧
    ∀u∈Icc (0:ℝ) (3/2), ∀v∈Icc (0:ℝ) (3/2),
      |Real.log (saddleChi v)-Real.log (saddleChi u)| ≤ C*|v-u| := by
  obtain ⟨C,hC,hLip⟩ := saddleChi_uniform_lipschitz
  have hlog (x y:ℝ) (hx:1/5≤x) (hy:1/5≤y) :
      |Real.log y-Real.log x| ≤ 5*|y-x| := by
    rcases le_total x y with hxy | hyx
    · have hxp:0<x := by linarith
      have H := Analysis.log_ordered_difference_le x y hxp hxy
      rw [abs_of_nonneg H.1,abs_of_nonneg (sub_nonneg.mpr hxy)]
      have H' : (y-x)/x ≤ 5*(y-x) := (div_le_iff₀ hxp).mpr (by nlinarith)
      exact H.2.trans H'
    · have hyp:0<y := by linarith
      have H := Analysis.log_ordered_difference_le y x hyp hyx
      rw [abs_sub_comm,abs_sub_comm y x,abs_of_nonneg H.1,abs_of_nonneg (sub_nonneg.mpr hyx)]
      have H' : (x-y)/y ≤ 5*(x-y) := (div_le_iff₀ hyp).mpr (by nlinarith)
      exact H.2.trans H'
  refine ⟨5*C,by positivity,?_⟩
  intro u hu v hv
  calc _ ≤ 5*|saddleChi v-saddleChi u| := hlog _ _ (saddleChi_lower u hu) (saddleChi_lower v hv)
       _ ≤ 5*(C*|v-u|) := mul_le_mul_of_nonneg_left (hLip u hu v hv) (by norm_num)
       _ = _ := by ring

lemma adjacentProfileQ_pos (α:ℝ) (hα:α∈Ioc (0:ℝ) 3) : 0<adjacentProfileQ α := by
  have hu : (3-α)/2∈Icc (0:ℝ) (3/2) := by constructor <;> linarith [hα.1,hα.2]
  have hl := saddleChi_lower _ hu
  unfold adjacentProfileQ
  exact mul_pos (mul_pos (by norm_num) hα.1) (by linarith only [hl])

lemma adjacentProfileQ_three : adjacentProfileQ 3=12/5 := by
  norm_num [adjacentProfileQ,saddleChi_zero]

lemma logDegreeProfile_hasDerivAt (α:ℝ) (hα:α∈Ioo (0:ℝ) 3) :
    HasDerivAt logDegreeProfile (-Real.log (adjacentProfileQ α)) α := by
  let u:ℝ := (3-α)/2
  let z:ℝ := saddleZeta u
  let b:ℝ := (deriv unscaledMean z)⁻¹ * (-(1:ℝ)/2)
  have hu : u∈Ioo (0:ℝ) (3/2) := by dsimp [u];constructor <;> linarith [hα.1,hα.2]
  have hz : z∈Icc (0:ℝ) (r 0) := (saddleZeta_spec u ⟨hu.1.le,hu.2.le⟩).1
  have hzp : 0<z := saddleZeta_pos u hu.1 hu.2.le
  have hdz : HasDerivAt (fun t:ℝ=>saddleZeta ((3-t)/2)) b α := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, one_div, u, z, b] using
      (saddleZeta_hasDerivAt u hu).comp α (((hasDerivAt_const α 3).sub (hasDerivAt_id α)).div_const 2)
  have hp : HasDerivAt (fun t:ℝ=>2*unscaledLogPotential (saddleZeta ((3-t)/2))) (2*saddleChi u*b) α := by
    convert ((unscaledLogPotential_hasDerivAt z hz).comp α hdz).const_mul 2 using 1 <;> dsimp [saddleChi,z] <;> ring
  have hlogz := hdz.log hzp.ne'
  have h3 := (hasDerivAt_const α (3:ℝ)).sub (hasDerivAt_id α)
  have h2 := (hasDerivAt_id α).const_mul 2
  have h3p : 0<3-α := sub_pos.mpr hα.2
  have h2p : 0<2*α := by linarith [hα.1]
  have ht := (((hp.sub (h3.mul hlogz)).add (h3.mul (h3.log h3p.ne'))).add_const (3*Real.log 6)).sub
    ((hasDerivAt_id α).mul (h2.log h2p.ne'))
  have ht := ht.sub (h3.const_mul 2)
  convert ht using 1
  · ext t
    dsimp [logDegreeProfile,unscaledLogPotential]
    ring
  have hch := saddleChi_mul_saddleZeta u ⟨hu.1.le,hu.2.le⟩
  have hchip : 0<saddleChi u := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/5) (saddleChi_lower u ⟨hu.1.le,hu.2.le⟩)
  have hq : adjacentProfileQ α=(2*α)*((3-α)/z) := by
    dsimp [adjacentProfileQ]
    change 4*α*saddleChi u = (2*α)*((3-α)/z)
    have hch' : z * saddleChi u = (3-α)/2 := hch
    field_simp [hzp.ne']
    nlinarith only [congrArg (fun x:ℝ=>x*α) hch']
  rw [hq,Real.log_mul h2p.ne' (div_ne_zero h3p.ne' hzp.ne'), Real.log_div h3p.ne' hzp.ne']
  dsimp [u,z] at *
  field_simp [hα.1.ne',h3p.ne',hzp.ne']
  nlinarith only [congrArg (fun x:ℝ=>x*b) hch]

lemma adjacentProfileQ_log_variation : ∃C:ℝ,0<C ∧
    ∀α∈Ioo (0:ℝ) 3, ∀β∈Ioo (0:ℝ) 3, α/2≤β →
      |Real.log (adjacentProfileQ β)-Real.log (adjacentProfileQ α)| ≤
        (2/α+C)*|β-α| := by
  obtain ⟨C,hC,hχ⟩ := saddleChi_log_lipschitz
  refine ⟨C/2,by positivity,?_⟩
  intro α hα β hβ hhalf
  have hχa : (3-α)/2∈Icc (0:ℝ) (3/2) := by constructor <;> linarith [hα.1,hα.2]
  have hχb : (3-β)/2∈Icc (0:ℝ) (3/2) := by constructor <;> linarith [hβ.1,hβ.2]
  have hχap : 0<saddleChi ((3-α)/2) := lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (saddleChi_lower _ hχa)
  have hχbp : 0<saddleChi ((3-β)/2) := lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (saddleChi_lower _ hχb)
  have hl : |Real.log β-Real.log α| ≤ (2/α)*|β-α| := by
    rcases le_total α β with hab | hba
    · have H := Analysis.log_ordered_difference_le α β hα.1 hab
      rw [abs_of_nonneg H.1,abs_of_nonneg (sub_nonneg.mpr hab)]
      have H' : (β-α)/α≤(2/α)*(β-α) := by
        have he : 0≤(β-α)/α := div_nonneg (sub_nonneg.mpr hab) hα.1.le
        calc _ ≤ 2*((β-α)/α) := by linarith
             _ = _ := by ring
      exact H.2.trans H'
    · have H := Analysis.log_ordered_difference_le β α hβ.1 hba
      rw [abs_sub_comm,abs_sub_comm β α,abs_of_nonneg H.1,abs_of_nonneg (sub_nonneg.mpr hba)]
      have H' : (α-β)/β≤(2/α)*(α-β) := by
        calc _ ≤ (α-β)/(α/2) := div_le_div_of_nonneg_left (sub_nonneg.mpr hba) (half_pos hα.1) hhalf
             _ = _ := by ring
      exact H.2.trans H'
  have hχbound := hχ _ hχa _ hχb
  have habs : |(3-β)/2-(3-α)/2|=|β-α|/2 := by
    rw [show (3-β)/2-(3-α)/2=-(β-α)/2 by ring,abs_div,abs_neg,abs_of_pos (by norm_num:(0:ℝ)<2)]
  rw [habs] at hχbound
  have hqa : Real.log (adjacentProfileQ α)=Real.log 4+Real.log α+Real.log (saddleChi ((3-α)/2)) := by
    rw [adjacentProfileQ,Real.log_mul (mul_pos (by norm_num) hα.1).ne' hχap.ne',Real.log_mul (by norm_num) hα.1.ne']
  have hqb : Real.log (adjacentProfileQ β)=Real.log 4+Real.log β+Real.log (saddleChi ((3-β)/2)) := by
    rw [adjacentProfileQ,Real.log_mul (mul_pos (by norm_num) hβ.1).ne' hχbp.ne',Real.log_mul (by norm_num) hβ.1.ne']
  rw [hqa,hqb]
  calc _ = |(Real.log β-Real.log α)+(Real.log (saddleChi ((3-β)/2))-Real.log (saddleChi ((3-α)/2)))| := by congr 1;ring
       _ ≤ |Real.log β-Real.log α|+|Real.log (saddleChi ((3-β)/2))-Real.log (saddleChi ((3-α)/2))| := abs_add_le _ _
       _ ≤ (2/α)*|β-α|+C*(|β-α|/2) := add_le_add hl hχbound
       _ = _ := by ring

lemma logDegreeProfile_secant_remainder : ∃C:ℝ,0<C ∧
    ∀α∈Ioo (0:ℝ) 3, ∀a b:ℝ, a∈Ioo (0:ℝ) 3 → b∈Ioo (0:ℝ) 3 →
      a≤b → α/2≤a →
      |logDegreeProfile b-logDegreeProfile a+(b-a)*Real.log (adjacentProfileQ α)| ≤
        (2/α+C)*max |a-α| |b-α| *(b-a) := by
  obtain ⟨C,hC,hlog⟩ := adjacentProfileQ_log_variation
  refine ⟨C,hC,?_⟩
  intro α hα a b ha hb hab hhalf
  let F : ℝ→ℝ := fun t=>logDegreeProfile t+t*Real.log (adjacentProfileQ α)
  have hD (t:ℝ) (ht:t∈Icc a b) :
      HasDerivAt F (-Real.log (adjacentProfileQ t)+Real.log (adjacentProfileQ α)) t := by
    convert (logDegreeProfile_hasDerivAt t ⟨ha.1.trans_le ht.1,ht.2.trans_lt hb.2⟩).add
      ((hasDerivAt_id t).mul_const (Real.log (adjacentProfileQ α))) using 1 <;> simp [F,Pi.add_def]
  have he := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht=>(hD t ht).hasDerivWithinAt) (C:=(2/α+C)*max |a-α| |b-α|) ?_
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩)
  · rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at he
    convert he using 1 <;> dsimp [F] <;> congr 1 <;> ring
  · intro t ht
    rw [Real.norm_eq_abs,show -Real.log (adjacentProfileQ t)+Real.log (adjacentProfileQ α)=
      -(Real.log (adjacentProfileQ t)-Real.log (adjacentProfileQ α)) by ring,abs_neg]
    have he := hlog α hα t ⟨ha.1.trans_le ht.1,ht.2.trans_lt hb.2⟩ (hhalf.trans ht.1)
    have hx : |t-α| ≤ max |a-α| |b-α| := by
      rw [abs_le]
      constructor
      · have H := neg_abs_le (a-α)
        linarith [le_max_left |a-α| |b-α|,ht.1]
      · have H := le_abs_self (b-α)
        linarith [le_max_right |a-α| |b-α|,ht.2]
    exact he.trans (mul_le_mul_of_nonneg_left hx (add_nonneg (div_nonneg (by norm_num) hα.1.le) hC.le))

end WP.Coefficients
