import WPFormalization.Volumes.OriginNormalization
import WPFormalization.External.FixedCusps
/-! Identification of the classical fixed-cusp universal constant.
The old MZ result supplies an unknown common constant. The actual first
marked prefactor and exact zero-parameter normalizations force that
constant to equal one in the present scale; the fixed-n errors then follow. -/
noncomputable section
namespace WP
open Set Filter
open scoped Topology
lemma real_tendsto_of_abs_error (f ε : ℕ → ℝ) (c : ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hb : ∀ᶠ g in atTop, |f g-c|≤ε g) :
    Tendsto f atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨G,hG⟩ := eventually_atTop.mp (hb.and (hε.eventually (gt_mem_nhds hδ)))
  refine ⟨G,?_⟩
  intro g hg
  simpa only [Real.dist_eq] using (hG g hg).1.trans_lt (hG g hg).2
lemma inverse_genus_tendsto_zero : Tendsto (fun g : ℕ => (g:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma log_genus_over_genus_tendsto_zero :
    Tendsto (fun g : ℕ => Real.log ((g:ℝ)+1)/(g:ℝ)) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def,pow_one,one_mul,add_neg_cancel_right] using ht
lemma volume_one_over_leading_tendsto (P : PsiTheory) :
    Tendsto (fun g : ℕ => volumeModel P g 1/leadingVolume g 1) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hb⟩ := absolute_prefactor P 1 (by norm_num)
  have ht : Tendsto (fun g : ℕ => C*Real.log ((g:ℝ)+1)/(g:ℝ)) atTop (𝓝 0) := by
    simpa only [←mul_div_assoc,mul_zero] using log_genus_over_genus_tendsto_zero.const_mul C
  apply real_tendsto_of_abs_error _ _ 1 ht
  apply eventually_atTop.mpr
  refine ⟨G+2,?_⟩
  intro g hg
  rw [volume_one_over_leading P g (by omega)]
  simpa only [XR_zero] using hb g (by omega) 0 ⟨le_rfl,y₀_pos⟩
lemma leadingVolume_one_over_fixed_scale_tendsto :
    Tendsto (fun g : ℕ => leadingVolume g 1/fixedCuspLeadingScale g 1) atTop (𝓝 1) := by
  have hbase : Tendsto (fun g : ℕ => (2:ℝ)*g) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hlin : Tendsto (fun g : ℕ => 2*(g:ℝ)-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using hbase.atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1:ℝ)) atTop (𝓝 (-1)))
  have hinv := tendsto_inv_atTop_zero.comp hlin
  have hs : Tendsto (fun g : ℕ => Real.sqrt (1+1/(2*(g:ℝ)-1))) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add hinv
    simpa only [Function.comp_def,one_div,add_zero,Real.sqrt_one] using ht.sqrt
  apply Filter.Tendsto.congr' _ hs
  apply eventually_atTop.mpr
  exact ⟨2,fun g hg => (leadingVolume_one_over_fixed_scale g hg).symm⟩
lemma volume_one_over_fixed_scale_tendsto (P : PsiTheory) :
    Tendsto (fun g : ℕ => volumeModel P g 1/fixedCuspLeadingScale g 1) atTop (𝓝 1) := by
  have ht := (volume_one_over_leading_tendsto P).mul leadingVolume_one_over_fixed_scale_tendsto
  have he : (fun g : ℕ => (volumeModel P g 1/leadingVolume g 1)*
      (leadingVolume g 1/fixedCuspLeadingScale g 1)) =ᶠ[atTop]
      (fun g : ℕ => volumeModel P g 1/fixedCuspLeadingScale g 1) := by
    apply eventually_atTop.mpr
    refine ⟨2,?_⟩
    intro g hg
    have hs : Stable g 1 := by unfold Stable;omega
    have h0 : (0:ℝ)∈Ico 0 y₀ := ⟨le_rfl,y₀_pos⟩
    have hM := markedModel_pos_parameter g 1 hs 0 h0
    have hL : 0<leadingVolume g 1 := by
      rw [←markedModel_one_zero_leading g (by omega)]
      positivity
    have hgR : 0<(g:ℝ) := by exact_mod_cast (show 0<g by omega)
    have hS : 0<fixedCuspLeadingScale g 1 := by unfold fixedCuspLeadingScale;positivity
    field_simp [hL.ne',hS.ne']
  simpa only [one_mul] using Filter.Tendsto.congr' he ht
lemma fixed_cusp_unknown_constant_tendsto (P : PsiTheory) (c C : ℝ) (G : ℕ)
    (hb : ∀ g≥G, |volumeModel P g 1/fixedCuspLeadingScale g 1-c|≤C/g) :
    Tendsto (fun g : ℕ => volumeModel P g 1/fixedCuspLeadingScale g 1) atTop (𝓝 c) := by
  have ht : Tendsto (fun g : ℕ => C/(g:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using inverse_genus_tendsto_zero.const_mul C
  exact real_tendsto_of_abs_error _ _ c ht (eventually_atTop.mpr ⟨G,hb⟩)
lemma zograf_constant_proof (P : PsiTheory) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      |volumeModel P g n /
        ((2*g+n-3).factorial*(4*Real.pi^2)^(2*g+n-3)/Real.sqrt (Real.pi*g))-1| ≤ C/g := by
  obtain ⟨c,hc,hall⟩ := External.fixed_cusps_universal_leading P
  obtain ⟨C,hC,G,hb⟩ := hall 1
  have hlim : Tendsto (fun g : ℕ => volumeModel P g 1/fixedCuspLeadingScale g 1) atTop (𝓝 c) := by
    apply fixed_cusp_unknown_constant_tendsto P c C G
    simpa only [fixedCuspLeadingScale] using hb
  have hval : c=1 := tendsto_nhds_unique hlim (volume_one_over_fixed_scale_tendsto P)
  subst c
  exact hall n
end WP
