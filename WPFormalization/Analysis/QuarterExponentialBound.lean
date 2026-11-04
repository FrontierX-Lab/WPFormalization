import WPFormalization.Analysis.FiniteWatson
/-! The actual quarter-power length factor is absorbed into a smaller square-root exponential. -/
noncomputable section
namespace WP.Analysis
lemma quarter_power_exp_neg_sqrt_bound (a h:ℝ) (ha:0<a) (hh:1≤h) :
    Real.sqrt (Real.sqrt h)*Real.exp (-a*Real.sqrt h)≤
      (4/a)*Real.exp (-(a/2)*Real.sqrt h) := by
  have hs1:1≤Real.sqrt h:=by simpa using Real.sqrt_le_sqrt hh
  have he:=normalized_outer_exp_factorial_bound (1/2) (a/2) (Real.sqrt h) (by norm_num) (half_pos ha) hs1 0
  rw[←Real.sqrt_eq_rpow] at he
  have hb:Real.sqrt (Real.sqrt h)*Real.exp (-((a/2)*Real.sqrt h))≤4/a:=by
    convert he using 1 <;>norm_num <;>field_simp <;>ring
  have hexp:Real.exp (-a*Real.sqrt h)=
      Real.exp (-((a/2)*Real.sqrt h))*Real.exp (-((a/2)*Real.sqrt h)) := by
    rw[←Real.exp_add]
    congr 1
    ring
  rw[hexp,←mul_assoc]
  exact (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le).trans_eq (by congr 1;ring)
end WP.Analysis
