import WPFormalization.Analysis.QuadraticRemainder
import WPFormalization.Analysis.Taylor
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma tiny_circle_coefficient_error_bound (F M:ℂ→ℂ)(h d C a cQ κ Qnorm:ℝ)(k:ℕ)
    (hh:0<h)(hd:0<d)(hC:0≤C)(hcQ:0<cQ)(hκ:0≤κ)(hκd:κ≤d/2)
    (hk:(k:ℝ)≤κ*Real.sqrt h)
    (hQ:cQ*(2*h)^k/(k.factorial:ℝ)≤Qnorm)
    (hF:AnalyticOnNhd ℂ F (Metric.closedBall 0 (d/(4*Real.sqrt h))))
    (hM:AnalyticOnNhd ℂ M (Metric.closedBall 0 (d/(4*Real.sqrt h))))
    (hbound:∀z:ℂ,‖z‖≤d/(4*Real.sqrt h)→‖F z-M z‖≤C*Real.exp (-a*Real.sqrt h)):
    ‖WP.coeff F k-WP.coeff M k‖/Qnorm≤(C/cQ)*Real.exp (-a*Real.sqrt h):=by
  let r:ℝ:=d/(4*Real.sqrt h)
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hr:0<r:=by dsimp[r];positivity
  have hfac:0<(k.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos k
  have hQpos:0<Qnorm:=lt_of_lt_of_le (by positivity) hQ
  have hF0:AnalyticAt ℂ F 0:=hF 0 (by simpa only[Metric.mem_closedBall,dist_self] using hr.le)
  have hM0:AnalyticAt ℂ M 0:=hM 0 (by simpa only[Metric.mem_closedBall,dist_self] using hr.le)
  have hcoef:WP.coeff (fun z:ℂ=>F z-M z) k=WP.coeff F k-WP.coeff M k:=by
    have he:=congrArg (PowerSeries.coeff k) (taylor_sub hF0 hM0)
    simpa only[taylor_coeff,map_sub] using he
  have hc:=coeff_norm_le_circle_bound (fun z:ℂ=>F z-M z) r (C*Real.exp (-a*Real.sqrt h)) hr
    (hF.sub hM).differentiableOn (fun z hz=>hbound z (by
      have hn:‖z‖=r:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
      exact hn.le)) k
  rw[hcoef] at hc
  have hkr:(k.factorial:ℝ)≤(2*h*r)^k:=by
    have hkp:(k.factorial:ℝ)≤(k:ℝ)^k:=by exact_mod_cast Nat.factorial_le_pow k
    have hker:(k:ℝ)≤2*h*r:=by
      have hτ:(k:ℝ)≤(d/2)*Real.sqrt h:=hk.trans (mul_le_mul_of_nonneg_right hκd hs.le)
      have he:2*h*r=(d/2)*Real.sqrt h:=by
        dsimp[r]
        have hhS:=Real.sq_sqrt hh.le
        field_simp
        nlinarith
      rwa[he]
    exact hkp.trans (pow_le_pow_left₀ (Nat.cast_nonneg k) hker k)
  have hQr:cQ≤Qnorm*r^k:=by
    calc
      _=cQ*(k.factorial:ℝ)/(k.factorial:ℝ):=by field_simp
      _≤cQ*(2*h*r)^k/(k.factorial:ℝ):=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkr hcQ.le) hfac.le
      _=(cQ*(2*h)^k/(k.factorial:ℝ))*r^k:=by rw[mul_pow];ring
      _≤Qnorm*r^k:=mul_le_mul_of_nonneg_right hQ (pow_nonneg hr.le k)
  calc
    _≤(C*Real.exp (-a*Real.sqrt h)/r^k)/Qnorm:=div_le_div_of_nonneg_right hc hQpos.le
    _=(C*Real.exp (-a*Real.sqrt h))/(Qnorm*r^k):=by ring
    _≤(C*Real.exp (-a*Real.sqrt h))/cQ:=div_le_div_of_nonneg_left (by positivity) hcQ hQr
    _=(C/cQ)*Real.exp (-a*Real.sqrt h):=by ring
end WP.Analysis
