import WPFormalization.External.PainleveAnalyticData
import Mathlib

/-! O(x^-4) decay on a selected imaginary ray forces the corresponding
classical CCH lateral parameter to vanish. This is proved by the actual
parameter limit and a norm bound, not imposed as a matching hypothesis. -/
noncomputable section
namespace WP.Analysis
open Complex Filter
open WP.External.PainleveAnalytic

lemma cch_parameter_eq_zero_of_ray_decay (D : CCHData) (s : Side) (h : ℂ → ℂ)
    (hn : NativeSmall s h) (C R : ℝ)
    (hd : ∀t:ℝ,R≤t → ‖h (ray (sideSign s*Real.pi/2) t)‖≤C*Real.rpow t (-4)) :
    D.parameter s h=0 := by
  have hpow : Tendsto (fun t:ℝ => t^(-7/2:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/2)
  have hlim : Tendsto (fun t:ℝ => C*t^(-7/2:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  have hzero : Tendsto (fun t:ℝ => Complex.sqrt (ray (sideSign s*Real.pi/2) t)*
      Complex.exp (ray (sideSign s*Real.pi/2) t)*h (ray (sideSign s*Real.pi/2) t)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hlim
    filter_upwards [eventually_ge_atTop R,eventually_ge_atTop (1:ℝ)] with t htR ht1
    have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht1
    have hNR : ‖ray (sideSign s*Real.pi/2) t‖=t := by
      unfold ray
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0,Complex.norm_exp]
      simp
    have hRe : (ray (sideSign s*Real.pi/2) t).re=0 := by
      cases s <;> simp [sideSign,ray,Complex.exp_re,neg_div]
    have hNE : ‖Complex.exp (ray (sideSign s*Real.pi/2) t)‖=1 := by rw [Complex.norm_exp,hRe,Real.exp_zero]
    have hNS : ‖Complex.sqrt (ray (sideSign s*Real.pi/2) t)‖=Real.sqrt t := by
      rw [Complex.sqrt,show (2⁻¹:ℂ)=((1/2:ℝ):ℂ) by norm_num,Complex.norm_cpow_real,hNR,←Real.sqrt_eq_rpow]
    have hb := hd t htR
    simp only [Real.rpow_eq_pow] at hb
    rw [norm_mul,norm_mul,hNE,hNS,mul_one]
    calc
      _ ≤ Real.sqrt t*(C*t^(-4:ℝ)) := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
      _ = C*t^(-7/2:ℝ) := by
        have hp : t^(1/2:ℝ)*t^(-4:ℝ)=t^(-7/2:ℝ) := by
          rw [←Real.rpow_add ht0]
          congr 1
          norm_num
        rw [Real.sqrt_eq_rpow]
        calc
          _ = C*(t^(1/2:ℝ)*t^(-4:ℝ)) := by ring
          _ = _ := by rw [hp]
  exact tendsto_nhds_unique (D.parameter_limit s h hn) hzero
end WP.Analysis
