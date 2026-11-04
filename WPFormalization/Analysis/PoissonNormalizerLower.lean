import WPFormalization.Analysis.PoissonPhasePrefactor
/-! Elementary positive-saddle lower bounds. These are finite real
normalization inequalities; they do not assume any coefficient extraction
limit or uniform comparison theorem. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma poisson_saddle_prefactor_lower (h x s C:ℝ)(k:ℕ)
    (hh:0<h)(hx:0<x)(hk:0<k)(hC:0≤C)(hs:2*x-C*x^2≤ s):
    Real.exp (-C*h*x^2)*(2*h)^k/(k.factorial:ℝ)≤
      Real.exp (h*s)*x⁻¹^k*poissonCenter k:=by
  have hkR:0<(k:ℝ):=by exact_mod_cast hk
  let u:ℝ:=2*h*x/(k:ℝ)
  let q:ℝ:=((k:ℝ)/h)/x
  have hu:0<u:=by dsimp[u];positivity
  have hq:0<q:=by dsimp[q];positivity
  have hqu:q*u=2:=by dsimp[q,u];field_simp
  have hlog:Real.log q=Real.log 2-Real.log u:=by
    have he:=Real.log_mul hq.ne' hu.ne'
    rw[hqu] at he
    linarith
  have hent:k*Real.log u≤2*h*x-k:=by
    have ht:=mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu) hkR.le
    have he:(k:ℝ)*u=2*h*x:=by dsimp[u];field_simp
    nlinarith
  have hexp:(k:ℝ)*Real.log 2-C*h*x^2≤h*(s-(k:ℝ)/h+((k:ℝ)/h)*Real.log q):=by
    have he:h*(s-(k:ℝ)/h+((k:ℝ)/h)*Real.log q)=h*s-k+(k:ℝ)*Real.log q:=by field_simp
    rw[he,hlog]
    nlinarith[mul_le_mul_of_nonneg_left hs hh.le]
  rw[←poisson_phase_prefactor_real h x s k hh hx]
  change _≤Real.exp (h*(s-(k:ℝ)/h+((k:ℝ)/h)*Real.log q))*h^k/(k.factorial:ℝ)
  have ht:=mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (pow_nonneg hh.le k)
  have he:Real.exp ((k:ℝ)*Real.log 2-C*h*x^2)*h^k=
      Real.exp (-C*h*x^2)*(2*h)^k:=by
    rw[show (k:ℝ)*Real.log 2-C*h*x^2=(-C*h*x^2)+(k:ℝ)*Real.log 2 by ring,
      Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num:(0:ℝ)<2),mul_pow]
    ring
  rw[he] at ht
  exact div_le_div_of_nonneg_right ht (Nat.cast_nonneg k.factorial)
lemma poisson_saddle_normalizer_lower (h x s B v C τ:ℝ)(k:ℕ)
    (hh:0<h)(hx:0<x)(hv:0<v)(hk:0<k)(hC:0≤C)(hτ:0≤τ)
    (hs:2*x-C*x^2≤ s)(hB:1/2≤B)(hxk:h*x≤(k:ℝ))
    (hkτ:(k:ℝ)≤τ*Real.sqrt h)(hvx:v≤4*x):
    (Real.exp (-C*τ^2)/4)*(2*h)^k/(k.factorial:ℝ)≤
      (Real.exp (h*s)*x⁻¹^k*poissonCenter k)*(B*Real.sqrt (((k:ℝ)/h)/v)):=by
  have hkR:0<(k:ℝ):=by exact_mod_cast hk
  have hxl: x≤(k:ℝ)/h:=(le_div_iff₀ hh).mpr (by nlinarith[hxk])
  have hvr:(1/4:ℝ)≤((k:ℝ)/h)/v:=(le_div_iff₀ hv).mpr (by nlinarith[hvx,hxl])
  have hroot:(1/2:ℝ)≤Real.sqrt (((k:ℝ)/h)/v):=by
    have he:=Real.sqrt_le_sqrt hvr
    norm_num at he
    exact he
  have hbf:(1/4:ℝ)≤B*Real.sqrt (((k:ℝ)/h)/v):=by
    nlinarith[mul_le_mul hB hroot (by norm_num:(0:ℝ)≤1/2) (by linarith:(0:ℝ)≤B)]
  have hxτ:h*x^2≤τ^2:=by
    have hsq1:(h*x)^2≤(k:ℝ)^2:=pow_le_pow_left₀ (by positivity) hxk 2
    have hsq2:(k:ℝ)^2≤τ^2*h:=by
      have ht:=pow_le_pow_left₀ (Nat.cast_nonneg k) hkτ 2
      rw[mul_pow,Real.sq_sqrt hh.le] at ht
      exact ht
    apply (mul_le_mul_iff_right₀ hh).mp
    nlinarith[hsq1.trans hsq2]
  have he:Real.exp (-C*τ^2)≤Real.exp (-C*h*x^2):=by
    apply Real.exp_le_exp.mpr
    nlinarith[mul_le_mul_of_nonneg_left hxτ hC]
  have hpref:=poisson_saddle_prefactor_lower h x s C k hh hx hk hC hs
  have hscale:Real.exp (-C*τ^2)*(2*h)^k/(k.factorial:ℝ)≤Real.exp (h*s)*x⁻¹^k*poissonCenter k:=by
    apply le_trans _ hpref
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (by positivity)) (Nat.cast_nonneg k.factorial)
  have hprod:=mul_le_mul hscale hbf (by norm_num:(0:ℝ)≤1/4) (by dsimp[poissonCenter];positivity)
  convert hprod using 1 <;>ring
end WP.Analysis
