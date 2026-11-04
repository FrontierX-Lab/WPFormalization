import Mathlib
/-! The two genuine central error terms are bounded on the common
minimum scale by one polynomial-times-Gaussian-growth expression. -/
noncomputable section
namespace WP.Analysis
set_option autoImplicit false
lemma gaussian_core_two_term_le_polynomial (ρ C D E h m T:ℝ)
    (hρ:0<ρ)(hC:0<C)(hD:0<D)(hE:0<E)(hm:0 < m)(hmh:m≤h)(hT:1≤T):
    4*D*Real.sqrt (E/h)*Real.exp (256*C*T^2)+(8*C*D*T^3+4*D*T)/(ρ*Real.sqrt m)≤
      (4*D*Real.sqrt E+(8*C*D+4*D)/ρ)*(1+T)^3*Real.exp (256*C*T^2)/Real.sqrt m:=by
  have hh:0<h:=hm.trans_le hmh
  have hsm:0<Real.sqrt m:=Real.sqrt_pos.mpr hm
  have hT0:0≤T:=by linarith only[hT]
  have hpoly:1≤(1+T)^3:=one_le_pow₀ (by linarith only[hT])
  have hTc:T≤T^3:=by
    have ht2:1≤T^2:=one_le_pow₀ hT
    have ht3:=mul_le_mul_of_nonneg_left ht2 hT0
    nlinarith only[ht3]
  have hTpoly:T^3≤(1+T)^3:=pow_le_pow_left₀ hT0 (by linarith) 3
  have hTlin:T≤(1+T)^3:=hTc.trans hTpoly
  have hexp:1≤Real.exp (256*C*T^2):=Real.one_le_exp_iff.mpr (by positivity)
  have hroot:Real.sqrt (E/h)≤Real.sqrt E/Real.sqrt m:=by
    rw[Real.sqrt_div hE.le]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg E) hsm (Real.sqrt_le_sqrt hmh)
  have hfirst:4*D*Real.sqrt (E/h)*Real.exp (256*C*T^2)≤
      (4*D*Real.sqrt E)*(1+T)^3*Real.exp (256*C*T^2)/Real.sqrt m:=by
    calc
      _≤4*D*(Real.sqrt E/Real.sqrt m)*Real.exp (256*C*T^2):=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity:0≤4*D)) (Real.exp_pos _).le
      _=(4*D*Real.sqrt E)*Real.exp (256*C*T^2)/Real.sqrt m:=by ring
      _≤(4*D*Real.sqrt E)*(1+T)^3*Real.exp (256*C*T^2)/Real.sqrt m:=by
        apply div_le_div_of_nonneg_right _ hsm.le
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hpoly) (Real.exp_pos _).le
  have hnum:8*C*D*T^3+4*D*T≤(8*C*D+4*D)*(1+T)^3:=by
    have h₁:=mul_le_mul_of_nonneg_left hTpoly (by positivity:0≤8*C*D)
    have h₂:=mul_le_mul_of_nonneg_left hTlin (by positivity:0≤4*D)
    nlinarith only[h₁,h₂]
  have hsecond:(8*C*D*T^3+4*D*T)/(ρ*Real.sqrt m)≤
      ((8*C*D+4*D)/ρ)*(1+T)^3*Real.exp (256*C*T^2)/Real.sqrt m:=by
    calc
      _≤((8*C*D+4*D)*(1+T)^3)/(ρ*Real.sqrt m):=
        div_le_div_of_nonneg_right hnum (by positivity)
      _=((8*C*D+4*D)/ρ)*(1+T)^3/Real.sqrt m:=by ring
      _≤((8*C*D+4*D)/ρ)*(1+T)^3*Real.exp (256*C*T^2)/Real.sqrt m:=
        div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hexp) hsm.le
  exact (add_le_add hfirst hsecond).trans_eq (by ring)
end WP.Analysis
