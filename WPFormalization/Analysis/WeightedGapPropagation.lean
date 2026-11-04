import Mathlib
/-! A positive weighted monotone ratio propagates a bounded initial gap. -/
set_option autoImplicit false
noncomputable section
namespace WP.Analysis
lemma weighted_ratio_gap_lower (a b w v r:ℝ)(hw:0 < w)(hb:0 ≤ b)(hr:0 ≤ r)(hr1:r ≤ 1)
    (hgap:1+r ≤ a)(hmono:a*w ≤ b*v)(hweight:v ≤ (1+r/6)*w):
    1+r/2 ≤ b:=by
  have h1:(1+r)*w ≤ (b*(1+r/6))*w:=by
    calc
      _ ≤ a*w:=mul_le_mul_of_nonneg_right hgap hw.le
      _ ≤ b*v:=hmono
      _ ≤ b*((1+r/6)*w):=mul_le_mul_of_nonneg_left hweight hb
      _ = _:=by ring
  have h2:1+r ≤ b*(1+r/6):=(mul_le_mul_iff_left₀ hw).mp h1
  have h3:(1+r/2)*(1+r/6) ≤ 1+r:=by
    nlinarith only[mul_le_mul_of_nonneg_left hr1 hr,hr]
  exact (mul_le_mul_iff_left₀ (by positivity:0 < 1+r/6)).mp (h3.trans h2)
end WP.Analysis
