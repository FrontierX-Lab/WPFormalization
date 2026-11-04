import WPFormalization.Analysis.GaussianCharacteristicError
/-! On the genuine square-root analytic scale, normalized quadratic log
jets and bounded amplitudes give a uniform Gaussian error on the central
interval. The growing cutoff and cubic smallness conditions are explicit. -/
noncomputable section
namespace WP.Analysis
open Set Complex
set_option autoImplicit false

lemma scaled_gaussian_model_core_error (L A:ℂ→ℂ)(ρ C D m T:ℝ)
    (hρ:0<ρ)(hC:0<C)(hD:0<D)(hm:0 < m)(hT:1≤T)
    (hwindow:32*T≤ρ*Real.sqrt m)(hsmall:4*C*T^3/(ρ*Real.sqrt m)≤1)
    (hLa:AnalyticOnNhd ℂ L (Metric.ball 0 (ρ*Real.sqrt m)))
    (hAa:AnalyticOnNhd ℂ A (Metric.ball 0 (ρ*Real.sqrt m)))
    (hL0:L 0=0)(hL1:WP.coeff L 1=0)(hL2:WP.coeff L 2=(1/2:ℂ))(hA0:A 0=1)
    (hbL:∀w:ℂ,‖w‖<ρ*Real.sqrt m→‖L w‖≤C*‖w‖^2)
    (hbA:∀w:ℂ,‖w‖<ρ*Real.sqrt m→‖A w‖≤D)
    (t:ℝ)(ht:|t|≤T):
    ‖Complex.exp (L ((t:ℂ)*Complex.I))*A ((t:ℂ)*Complex.I)-Complex.exp (-(t:ℂ)^2/2)‖≤
      (8*C*D*T^3+4*D*T)/(ρ*Real.sqrt m):=by
  let R:ℝ:=ρ*Real.sqrt m/2
  have hs:0<Real.sqrt m:=Real.sqrt_pos.mpr hm
  have hR:0<R:=by dsimp[R];positivity
  have hRp:R<ρ*Real.sqrt m:=by dsimp[R];nlinarith[mul_pos hρ hs]
  have hTp:0<T:=zero_lt_one.trans_le hT
  have hTR:T≤R/2:=by dsimp[R];linarith
  have hLc:DifferentiableOn ℂ L (Metric.closedBall 0 R):=by
    intro z hz
    have hn:‖z‖≤R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    exact (hLa z (by simpa only[Metric.mem_ball,dist_zero_right] using hn.trans_lt hRp)).differentiableAt.differentiableWithinAt
  have hAc:DifferentiableOn ℂ A (Metric.closedBall 0 R):=by
    intro z hz
    have hn:‖z‖≤R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    exact (hAa z (by simpa only[Metric.mem_ball,dist_zero_right] using hn.trans_lt hRp)).differentiableAt.differentiableWithinAt
  have hLs:∀z∈Metric.sphere (0:ℂ) R,‖L z‖≤C*R^2:=by
    intro z hz
    have hn:‖z‖=R:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
    simpa only[hn] using hbL z (hn.trans_lt hRp)
  have hAs:∀z∈Metric.sphere (0:ℂ) R,‖A z‖≤D:=by
    intro z hz
    have hn:‖z‖=R:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
    exact hbA z (hn.trans_lt hRp)
  have hn:‖(t:ℂ)*Complex.I‖=|t|:=by rw[norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hAt:‖A ((t:ℂ)*Complex.I)‖≤D:=hbA _ (by rw[hn];exact ht.trans_lt (hTR.trans_lt (by dsimp[R];nlinarith[mul_pos hρ hs])))
  have hfactor:2*(C*R^2)/R^3=4*C/(ρ*Real.sqrt m):=by dsimp[R];field_simp;ring
  have hη:(2*(C*R^2)/R^3)*|t|^3≤1:=by
    rw[hfactor]
    have hpow:|t|^3≤T^3:=pow_le_pow_left₀ (abs_nonneg t) ht 3
    have hb:=mul_le_mul_of_nonneg_left hpow (by positivity:0≤4*C/(ρ*Real.sqrt m))
    exact hb.trans (by simpa only[div_mul_eq_mul_div] using hsmall)
  have hc0:WP.coeff L 0=0:=by simpa only[WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one] using hL0
  have he:=gaussian_characteristic_local_bound L A R (C*R^2) D hR (by positivity) hD.le
    hLc hAc hLs hAs hc0 hL1 hL2 hA0 t (ht.trans hTR) hη hAt
  have hphase:Complex.exp (((-t^2/2:ℝ):ℂ))=Complex.exp (-(t:ℂ)^2/2):=by
    congr 1
    push_cast
    ring
  rw[hphase] at he
  have hcoef₁:4*(C*R^2)*D/R^3=8*C*D/(ρ*Real.sqrt m):=by dsimp[R];field_simp;ring
  have hcoef₂:2*D/R=4*D/(ρ*Real.sqrt m):=by dsimp[R];field_simp;ring
  rw[hcoef₁,hcoef₂] at he
  have hexp:Real.exp (-t^2/2)≤1:=Real.exp_le_one_iff.mpr (by nlinarith[sq_nonneg t])
  have hb:8*C*D/(ρ*Real.sqrt m)*|t|^3+4*D/(ρ*Real.sqrt m)*|t|≤
      (8*C*D*T^3+4*D*T)/(ρ*Real.sqrt m):=by
    have hpow:|t|^3≤T^3:=pow_le_pow_left₀ (abs_nonneg t) ht 3
    have h₁:=mul_le_mul_of_nonneg_left hpow (by positivity:0≤8*C*D/(ρ*Real.sqrt m))
    have h₂:=mul_le_mul_of_nonneg_left ht (by positivity:0≤4*D/(ρ*Real.sqrt m))
    calc
      _≤8*C*D/(ρ*Real.sqrt m)*T^3+4*D/(ρ*Real.sqrt m)*T:=add_le_add h₁ h₂
      _=_:=by ring
  apply he.trans
  exact (mul_le_of_le_one_left (by positivity) hexp).trans hb
end WP.Analysis
