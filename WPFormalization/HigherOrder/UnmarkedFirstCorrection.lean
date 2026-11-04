import WPFormalization.HigherOrder.UnmarkedVolumeProof
import WPFormalization.External.FixedCuspsFirstCorrection
import WPFormalization.Volumes.FixedCuspProof
/-! The fixed-n=0 sharp correction. Its unknown classical normalization is
identified from the proved local unmarked expansion; c=1 is not admitted.
The only new deferred input is the separately registered classical MZ first
correction. Uniform-in-n estimates are not part of that input. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology

lemma leadingVolume_zero_eq_fixed_scale (g:ℕ)(hg:2≤g):
    leadingVolume g 0=(2*g-3).factorial*(4*Real.pi^2)^(2*g-3)/Real.sqrt (Real.pi*g):=by
  have he:2*(g:ℝ)-2=((2*g-3:ℕ):ℝ)+1:=by
    rw[Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only[leadingVolume,ite_true,he,Real.Gamma_nat_eq_factorial]

lemma unmarked_ratio_tendsto_one (P:PsiTheory):
    Tendsto (fun g:ℕ=>volumeModel P g 0/leadingVolume g 0) atTop (𝓝 (1:ℝ)):=by
  obtain ⟨C,B,c,hC,hB,hc,G,hG,_,herr,_⟩:=unmarked_absolute_expansion_proof P
  have hs:=Analysis.complexity_real_tendsto_atTop 1
  have hzero:Tendsto (fun g:ℕ=>C*B/(complexity g 1:ℝ)) atTop (𝓝 (0:ℝ)):=by
    simpa only[Function.comp_def,div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero.comp hs).const_mul (C*B)
  apply real_tendsto_of_abs_error _ _ 1 hzero
  filter_upwards[eventually_ge_atTop G] with g hg
  have he:=herr g hg 0 (by simp only[Nat.cast_zero];positivity)
  simpa only[Finset.sum_range_one,unmarkedCoefficient_zero,pow_zero,div_one,Nat.zero_add,
    Nat.factorial_one,Nat.cast_one,one_pow,mul_one,pow_one] using he

lemma normalization_eq_one_of_first_limit (F:ℕ→ℝ)(c d:ℝ)(hc:0<c)
    (hF:Tendsto F atTop (𝓝 (1:ℝ)))
    (hfirst:Tendsto (fun g:ℕ=>(g:ℝ)*(F g/c-1)) atTop (𝓝 d)):
    c=1:=by
  have ht:Tendsto (fun g:ℕ=>((g:ℝ)*(F g/c-1))*(g:ℝ)⁻¹) atTop (𝓝 (0:ℝ)):=by
    simpa only[mul_zero] using hfirst.mul inverse_genus_tendsto_zero
  have he:(fun g:ℕ=>((g:ℝ)*(F g/c-1))*(g:ℝ)⁻¹)=ᶠ[atTop]
      (fun g:ℕ=>F g/c-1):=by
    filter_upwards[eventually_ge_atTop 1] with g hg
    have hg0:(g:ℝ)≠0:=by exact_mod_cast (show g≠0 by omega)
    field_simp
  have hz:Tendsto (fun g:ℕ=>F g/c-1) atTop (𝓝 (0:ℝ)):=ht.congr' he
  have hone:Tendsto (fun g:ℕ=>F g/c) atTop (𝓝 (1:ℝ)):=by
    simpa only[sub_add_cancel,zero_add] using hz.add_const 1
  have hec:(1:ℝ)/c=1:=tendsto_nhds_unique (hF.div_const c) hone
  simpa only[one_mul] using ((div_eq_iff hc.ne').mp hec).symm

lemma unmarked_first_correction_limit (P:PsiTheory):
    Tendsto (fun g:ℕ=>(g:ℝ)*(volumeModel P g 0/leadingVolume g 0-1)) atTop
      (𝓝 (7/12-17/(6*Real.pi^2))):=by
  let F:ℕ→ℝ:=fun g=>volumeModel P g 0/
    ((2*g-3).factorial*(4*Real.pi^2)^(2*g-3)/Real.sqrt (Real.pi*g))
  have he:(fun g:ℕ=>volumeModel P g 0/leadingVolume g 0)=ᶠ[atTop] F:=by
    filter_upwards[eventually_ge_atTop 2] with g hg
    rw[leadingVolume_zero_eq_fixed_scale g hg]
  have hF:Tendsto F atTop (𝓝 (1:ℝ)):=(unmarked_ratio_tendsto_one P).congr' he
  obtain ⟨c,hc,hfirst⟩:=External.fixed_zero_cusps_first_correction P
  change Tendsto (fun g:ℕ=>(g:ℝ)*(F g/c-1)) atTop _ at hfirst
  have hec:=normalization_eq_one_of_first_limit F c _ hc hF hfirst
  rw[hec] at hfirst
  simp only[div_one] at hfirst
  apply hfirst.congr'
  filter_upwards[he] with g hg
  rw[hg]

lemma first_correction_lower_constant_pos :
    (0:ℝ)<7/12-17/(6*Real.pi^2):=by
  have hpi:9<Real.pi^2:=by nlinarith[Real.pi_gt_three]
  have he:(17:ℝ)/(6*Real.pi^2)<7/12:=
    (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)
  linarith

lemma unmarked_abs_first_correction_limit (P:PsiTheory):
    Tendsto (fun g:ℕ=>(g:ℝ)*|volumeModel P g 0/leadingVolume g 0-1|) atTop
      (𝓝 (7/12-17/(6*Real.pi^2))):=by
  have he:=(unmarked_first_correction_limit P).abs
  have hn (g:ℕ):|(g:ℝ)|=(g:ℝ):=abs_of_nonneg (Nat.cast_nonneg g)
  simpa only[abs_mul,hn,abs_of_pos first_correction_lower_constant_pos] using he
end WP.HigherOrder
