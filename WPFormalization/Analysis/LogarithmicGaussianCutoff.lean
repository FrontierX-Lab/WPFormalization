import Mathlib
/-! A logarithmic Gaussian cutoff turns a polynomial-times-exponential
central error and Gaussian tails into a common polynomial rate. Its radius
and cubic-remainder conditions hold eventually on the same cutoff. -/
noncomputable section
set_option autoImplicit false
namespace WP.Analysis
open Filter
open scoped Topology

lemma log_fourth_eventually_le_rpow (s:ℝ)(hs:0<s):
    ∀ᶠ (x : ℝ) in atTop,(Real.log x)^4≤x^s:=by
  have ht:=(isLittleO_log_rpow_rpow_atTop (4:ℝ) hs).bound (by norm_num:(0:ℝ)<1)
  filter_upwards[ht,eventually_ge_atTop (1:ℝ)] with x hm hm1
  have hm0:0≤x:=by linarith
  have hp4:(Real.log x)^(4:ℝ)=(Real.log x)^4:=Real.rpow_natCast _ 4
  have hm': |(Real.log x)^4|≤x^s:=by
    simpa only[hp4,Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg hm0 _)] using hm
  exact (le_abs_self _).trans hm'

lemma logarithmic_gaussian_cutoff_core_rate (B:ℝ)(hB:0≤B):
    ∃a:ℝ,0<a ∧ a≤1 ∧ ∀ᶠ (x : ℝ) in atTop,
      0 < x ∧ 1≤Real.sqrt (a*Real.log x) ∧
      (1+Real.sqrt (a*Real.log x))^4*Real.exp (B*(Real.sqrt (a*Real.log x))^2)/Real.sqrt x≤
        16*x^(-1/4:ℝ):=by
  let a:ℝ:=1/(8*(B+1))
  have ha:0<a:=by dsimp[a];positivity
  have ha1:a≤1:=by dsimp[a];apply (div_le_one (by positivity:0<8*(B+1))).mpr;nlinarith
  have hBa:B*a≤1/8:=by
    dsimp[a]
    rw[mul_one_div]
    apply (div_le_iff₀ (by positivity:0<8*(B+1))).mpr
    nlinarith
  have hlogpow:=log_fourth_eventually_le_rpow (1/8) (by norm_num)
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards[hlogpow,Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (1/a)),
    eventually_gt_atTop (0:ℝ)] with x hpow hlog hm0
  have hl1:1≤Real.log x:=(le_max_left _ _).trans hlog
  have hla:1/a≤Real.log x:=(le_max_right _ _).trans hlog
  let T:ℝ:=Real.sqrt (a*Real.log x)
  have hlog0:0≤Real.log x:=by linarith
  have hT0:0≤T:=Real.sqrt_nonneg _
  have hT2:T^2=a*Real.log x:=Real.sq_sqrt (mul_nonneg ha.le hlog0)
  have hT1:1≤T:=by
    have hh:1≤a*Real.log x:=by simpa only[mul_comm] using (div_le_iff₀ ha).mp hla
    nlinarith
  have hTl:T≤Real.log x:=by nlinarith[mul_le_mul_of_nonneg_right ha1 hlog0]
  have hp:(1+T)^4≤16*(Real.log x)^4:=by
    have hm:1+T≤2*Real.log x:=by linarith
    have hq:=pow_le_pow_left₀ (by positivity:0≤1+T) hm 4
    convert hq using 1 <;>ring
  have hexp:Real.exp (B*T^2)≤x^(1/8:ℝ):=by
    rw[Real.rpow_def_of_pos hm0,hT2]
    apply Real.exp_le_exp.mpr
    nlinarith[mul_le_mul_of_nonneg_right hBa hlog0]
  refine ⟨hm0,hT1,?_⟩
  change (1+T)^4*Real.exp (B*T^2)/Real.sqrt x≤_
  have hs:0<Real.sqrt x:=Real.sqrt_pos.mpr hm0
  calc
    _≤(16*(Real.log x)^4)*x^(1/8:ℝ)/Real.sqrt x:=
      div_le_div_of_nonneg_right (mul_le_mul hp hexp (Real.exp_pos _).le (by positivity)) hs.le
    _≤(16*x^(1/8:ℝ))*x^(1/8:ℝ)/Real.sqrt x:=by
      gcongr
    _=16*x^(-1/4:ℝ):=by
      rw[Real.sqrt_eq_rpow,mul_assoc,←Real.rpow_add hm0,mul_div_assoc,←Real.rpow_sub hm0]
      norm_num

lemma logarithmic_gaussian_cutoff_tail (a c x:ℝ)(ha : 0 ≤ a)(hm : 1 ≤ x):
    Real.exp (-c*(Real.sqrt (a*Real.log x))^2)=x^(-(c*a):ℝ):=by
  have hm0:0 < x:=zero_lt_one.trans_le hm
  rw[Real.sq_sqrt (mul_nonneg ha (Real.log_nonneg hm)),Real.rpow_def_of_pos hm0]
  congr 1
  ring


lemma logarithmic_gaussian_cutoff_window (a ρ A:ℝ)(ha:0<a)(ha1:a≤1)(hρ:0<ρ)(hA:0<A):
    ∀ᶠ (x:ℝ) in atTop,
      1≤Real.sqrt (a*Real.log x) ∧
      Real.sqrt (a*Real.log x)≤ρ*Real.sqrt x ∧
      A*(Real.sqrt (a*Real.log x))^3/Real.sqrt x≤1:=by
  let ε:ℝ:=min ρ (1/A)
  have hε:0<ε:=lt_min hρ (by positivity)
  have ht:Tendsto (fun x:ℝ=>x^(-3/8:ℝ)) atTop (𝓝 0):=by
    convert tendsto_rpow_neg_atTop (by norm_num:(0:ℝ)<3/8) using 1 <;>ring
  filter_upwards[log_fourth_eventually_le_rpow (1/8) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (1/a)),
    ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℝ)] with x hpow hlog hxsmall hx
  have hl1:1≤Real.log x:=(le_max_left _ _).trans hlog
  have hla:1/a≤Real.log x:=(le_max_right _ _).trans hlog
  let T:ℝ:=Real.sqrt (a*Real.log x)
  have hlog0:0≤Real.log x:=by linarith
  have hT0:0≤T:=Real.sqrt_nonneg _
  have hT2:T^2=a*Real.log x:=Real.sq_sqrt (mul_nonneg ha.le hlog0)
  have hT1:1≤T:=by
    have hh:1≤a*Real.log x:=by simpa only[mul_comm] using (div_le_iff₀ ha).mp hla
    nlinarith
  have hTl:T≤Real.log x:=by nlinarith[mul_le_mul_of_nonneg_right ha1 hlog0]
  have hTc:T^3≤(Real.log x)^4:=by
    have hb:T^3≤(Real.log x)^3:=pow_le_pow_left₀ hT0 hTl 3
    have hh:0≤(Real.log x)^3:=by positivity
    have he: (Real.log x)^3≤(Real.log x)^4:=by
      nlinarith[mul_le_mul_of_nonneg_left hl1 hh]
    exact hb.trans he
  have hs:0<Real.sqrt x:=Real.sqrt_pos.mpr hx
  have hratio:T^3/Real.sqrt x≤x^(-3/8:ℝ):=by
    calc
      _≤x^(1/8:ℝ)/Real.sqrt x:=div_le_div_of_nonneg_right (hTc.trans hpow) hs.le
      _=x^(-3/8:ℝ):=by
        rw[Real.sqrt_eq_rpow,←Real.rpow_sub hx]
        norm_num
  have hratε:T^3/Real.sqrt x≤ε:=hratio.trans hxsmall.le
  have hTle:T≤T^3:=by nlinarith[sq_nonneg T,mul_le_mul_of_nonneg_left hT1 hT0]
  have hlin:T/Real.sqrt x≤ρ:=
    ((div_le_div_of_nonneg_right hTle hs.le).trans hratε).trans (min_le_left _ _)
  have hcubic:A*T^3/Real.sqrt x≤1:=by
    have hquot:T^3/Real.sqrt x≤1/A:=hratε.trans (min_le_right _ _)
    have hmul:=mul_le_mul_of_nonneg_left hquot hA.le
    have hfactor:A*(1/A)=1:=by field_simp
    rw[hfactor] at hmul
    convert hmul using 1 <;>ring
  exact ⟨hT1,(div_le_iff₀ hs).mp hlin,hcubic⟩
end WP.Analysis
