import Mathlib
noncomputable section
namespace WP.PositiveConvolution
open Set MeasureTheory
lemma bernoulli_rpow_kernel_bound (H u:ℝ) (hH:16≤H) (hu:0≤u):
    (1+u)^(-H/8:ℝ) ≤ (1+H/16*u)^(-2:ℝ):=by
  have hp:1≤H/16:=by linarith
  have hb:=one_add_mul_self_le_rpow_one_add (by linarith:-(1:ℝ)≤u) hp
  have hu1:0<1+u:=by linarith
  have hbase:0<1+H/16*u:=by positivity
  have hh:=Real.rpow_le_rpow_of_nonpos hbase hb (by norm_num:(-2:ℝ)≤0)
  rw[←Real.rpow_mul hu1.le] at hh
  convert hh using 1 <;>ring
lemma critical_kernel_point_bound (H ε θ:ℝ) (hH:16≤H) (hε:0<ε):
    (1+θ^2/(4*ε^2))^(-H/8:ℝ) ≤
      (1+(Real.sqrt H/(8*ε)*θ)^2)⁻¹:=by
  have hHp:0<H:=by linarith
  have hb:=bernoulli_rpow_kernel_bound H (θ^2/(4*ε^2)) hH (by positivity)
  have he:1+H/16*(θ^2/(4*ε^2))=1+(Real.sqrt H/(8*ε)*θ)^2:=by
    rw[div_mul_eq_mul_div,mul_pow,div_pow,Real.sq_sqrt hHp.le]
    field_simp
    <;>ring
  rw[he,Real.rpow_neg (by positivity),Real.rpow_two] at hb
  have hbase:1≤1+(Real.sqrt H/(8*ε)*θ)^2:=by nlinarith[sq_nonneg (Real.sqrt H/(8*ε)*θ)]
  have hi:(1+(Real.sqrt H/(8*ε)*θ)^2)^2≥1+(Real.sqrt H/(8*ε)*θ)^2:=by nlinarith
  exact hb.trans (inv_anti₀ (by positivity) hi)
lemma rational_circle_integral_bound (k:ℝ) (hk:0<k):
    (∫θ:ℝ in (-Real.pi)..Real.pi,(1+(k*θ)^2)⁻¹) ≤ Real.pi/k:=by
  rw[intervalIntegral.integral_of_le (by linarith[Real.pi_pos]:-Real.pi≤Real.pi)]
  have hfull:=setIntegral_le_integral (s:=Ioc (-Real.pi) Real.pi)
    (integrable_inv_one_add_mul_sq hk.ne') (Filter.Eventually.of_forall (fun x=>by positivity))
  convert hfull using 1
  rw[integral_univ_inv_one_add_mul_sq,abs_of_pos hk]
lemma gaussian_circle_integral_bound (k:ℝ) (hk:0<k):
    (∫θ:ℝ in (-Real.pi)..Real.pi,Real.exp (-k*θ^2)) ≤ Real.sqrt (Real.pi/k):=by
  rw[intervalIntegral.integral_of_le (by linarith[Real.pi_pos]:-Real.pi≤Real.pi)]
  have hfull:=setIntegral_le_integral (s:=Ioc (-Real.pi) Real.pi)
    (integrable_exp_neg_mul_sq hk) (Filter.Eventually.of_forall (fun x=>(Real.exp_pos _).le))
  simpa only[integral_gaussian] using hfull
end WP.PositiveConvolution
namespace WP.PositiveConvolution
lemma geometric_power_sqrt_bound (q:ℝ) (H:ℕ) (hq0:0≤q) (hq:q≤1/2) (hH:2≤H):
    q^H≤4*q^2/Real.sqrt (H:ℝ):=by
  have hHp:0<(H:ℝ):=by exact_mod_cast (show 0<H by omega)
  have hs:0<Real.sqrt (H:ℝ):=Real.sqrt_pos.mpr hHp
  have ht:q^(H-2)≤(1/2:ℝ)^(H-2):=pow_le_pow_left₀ hq0 hq _
  have hnat:(H:ℝ)≤(2:ℝ)^H:=by exact_mod_cast (H.lt_two_pow_self).le
  have hsqrt:Real.sqrt (H:ℝ)≤(2:ℝ)^H:=
    (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1≤H by omega)))).trans hnat
  have hp2:(2:ℝ)^H=4*(2:ℝ)^(H-2):=by
    conv_lhs=>rw[show H=2+(H-2) by omega,pow_add]
    norm_num
  have hcan:(2:ℝ)^H*(1/2:ℝ)^(H-2)=4:=by
    rw[hp2,one_div_pow]
    field_simp
  have hfac:Real.sqrt (H:ℝ)*(1/2:ℝ)^(H-2)≤4:=
    (mul_le_mul_of_nonneg_right hsqrt (by positivity)).trans_eq hcan
  have he:q^H=q^2*q^(H-2):=by rw[←pow_add,show 2+(H-2)=H by omega]
  apply (le_div_iff₀ hs).2
  rw[he]
  calc
    q^2*q^(H-2)*Real.sqrt (H:ℝ) ≤ q^2*(1/2:ℝ)^(H-2)*Real.sqrt (H:ℝ):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (sq_nonneg _)) hs.le
    _ = q^2*(Real.sqrt (H:ℝ)*(1/2:ℝ)^(H-2)):=by ring
    _ ≤ q^2*4:=mul_le_mul_of_nonneg_left hfac (sq_nonneg _)
    _ = 4*q^2:=by ring
end WP.PositiveConvolution
namespace WP.PositiveConvolution
open Set MeasureTheory
lemma critical_circle_integral_bound (f:ℝ→ℝ) (hf:Continuous f) (H:ℕ)
    (ε δ C:ℝ) (hH:16≤H) (hε:0<ε) (hC:0≤C) (hq:C*Real.sqrt ε≤1/2)
    (hnear:∀θ∈Icc (-Real.pi) Real.pi,|θ|≤δ→
      f θ≤(1+θ^2/(4*ε^2))^(-(H:ℝ)/8:ℝ))
    (houter:∀θ∈Icc (-Real.pi) Real.pi,δ≤|θ|→f θ≤(C*Real.sqrt ε)^H):
    (∫θ:ℝ in (-Real.pi)..Real.pi,f θ)≤
      (8*Real.pi+8*Real.pi*C^2)*ε/Real.sqrt (H:ℝ):=by
  have hHp:0<(H:ℝ):=by exact_mod_cast (show 0<H by omega)
  have hs:0<Real.sqrt (H:ℝ):=Real.sqrt_pos.mpr hHp
  let k:ℝ:=Real.sqrt (H:ℝ)/(8*ε)
  have hk:0<k:=div_pos hs (mul_pos (by norm_num) hε)
  have hr:Continuous (fun θ:ℝ=>(1+(k*θ)^2)⁻¹):=by
    apply Continuous.inv₀ (by fun_prop)
    intro θ
    positivity
  have hp:∀θ∈Icc (-Real.pi) Real.pi,f θ≤(1+(k*θ)^2)⁻¹+(C*Real.sqrt ε)^H:=by
    intro θ hθ
    by_cases hn:|θ|≤δ
    · have hh:=(hnear θ hθ hn).trans
        (critical_kernel_point_bound (H:ℝ) ε θ (by exact_mod_cast hH) hε)
      exact hh.trans (le_add_of_nonneg_right (pow_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) _))
    · exact (houter θ hθ (le_of_not_ge hn)).trans
        (le_add_of_nonneg_left (by positivity))
  have hi:=intervalIntegral.integral_mono_on (μ:=volume)
    (by linarith[Real.pi_pos]:-Real.pi≤Real.pi) (hf.intervalIntegrable _ _)
    ((hr.add continuous_const).intervalIntegrable _ _) hp
  simp only[Pi.add_apply] at hi
  rw[intervalIntegral.integral_add (hr.intervalIntegrable _ _) (intervalIntegrable_const),
    intervalIntegral.integral_const,smul_eq_mul] at hi
  have hqpow:=geometric_power_sqrt_bound (C*Real.sqrt ε) H (mul_nonneg hC (Real.sqrt_nonneg _)) hq (by omega)
  have hq2:(C*Real.sqrt ε)^2=C^2*ε:=by rw[mul_pow,Real.sq_sqrt hε.le]
  rw[hq2] at hqpow
  have hrat:=rational_circle_integral_bound k hk
  calc
    _ ≤ (∫θ:ℝ in (-Real.pi)..Real.pi,(1+(k*θ)^2)⁻¹)+(Real.pi-(-Real.pi))*(C*Real.sqrt ε)^H:=hi
    _ ≤ Real.pi/k+(Real.pi-(-Real.pi))*(4*(C^2*ε)/Real.sqrt (H:ℝ)):=
      add_le_add hrat (mul_le_mul_of_nonneg_left hqpow (by linarith[Real.pi_pos]))
    _ = _:=by dsimp[k];field_simp;ring
end WP.PositiveConvolution
namespace WP.PositiveConvolution
lemma scaled_sqrt_le (ε H v B:ℝ) (hε:0<ε) (hH:0<H) (hv:0≤v) (hB:0≤B)
    (hbound:ε^2*v≤B*H):
    ε/Real.sqrt H*Real.sqrt v≤Real.sqrt B:=by
  have hs:0<Real.sqrt H:=Real.sqrt_pos.mpr hH
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw[mul_pow,div_pow,Real.sq_sqrt hH.le,Real.sq_sqrt hv,Real.sq_sqrt hB]
  rw[div_mul_eq_mul_div]
  exact (div_le_iff₀ hH).mpr hbound
end WP.PositiveConvolution
