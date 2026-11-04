import WPFormalization.Analysis.HarmonicLaw
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma coeff_norm_le_circle_bound (f:ℂ→ℂ)(R M:ℝ)(hR:0<R)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hM:∀z∈Metric.sphere (0:ℂ) R,‖f z‖≤M)(n:ℕ) : ‖WP.coeff f n‖≤M/R^n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    ((hf.mono Metric.closure_ball_subset_closedBall).diffContOnCl) hM
  have hFac : 0<(n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  unfold WP.coeff
  rw [norm_div]
  have hn : ‖(n.factorial:ℂ)‖=(n.factorial:ℝ) := by simp
  rw [hn]
  calc ‖iteratedDeriv n f 0‖/(n.factorial:ℝ) ≤ ((n.factorial:ℝ)*M/R^n)/(n.factorial:ℝ) := div_le_div_of_nonneg_right hd hFac.le
       _ = M/R^n := by field_simp
lemma complex_quadratic_remainder_bound (f:ℂ→ℂ)(R M:ℝ)(hR:0<R)(hM0:0≤M)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hM:∀z∈Metric.sphere (0:ℂ) R,‖f z‖≤M)(z:ℂ)(hz:‖z‖≤R/2) :
    ‖f z-(WP.coeff f 0+WP.coeff f 1*z+WP.coeff f 2*z^2)‖≤(2*M/R^3)*‖z‖^3 := by
  have hs := hasSum_coeff_on_ball f R (hf.mono Metric.ball_subset_closedBall) z (by linarith)
  have htail := (hasSum_nat_add_iff' 3).mpr hs
  let U : ℝ := ‖z‖/R
  let C : ℝ := M/R^3*‖z‖^3
  have hU0 : 0≤U := div_nonneg (norm_nonneg _) hR.le
  have hU : U≤1/2 := (div_le_iff₀ hR).mpr (by linarith)
  have hC : 0≤C := by dsimp [C]; positivity
  have hgeo := (hasSum_geometric_of_norm_lt_one (show ‖U‖<1 by rw [Real.norm_eq_abs,abs_of_nonneg hU0]; linarith)).mul_left C
  have hbound := htail.norm_le_of_bounded hgeo (fun n=>by
    rw [norm_mul,norm_pow]
    calc ‖WP.coeff f (n+3)‖*‖z‖^(n+3) ≤ (M/R^(n+3))*‖z‖^(n+3) :=
          mul_le_mul_of_nonneg_right (coeff_norm_le_circle_bound f R M hR hf hM (n+3)) (by positivity)
         _ = C*U^n := by dsimp [C,U]; rw [pow_add,pow_add,div_pow]; field_simp)
  have hden : 0<1-U := by linarith
  have hinv : (1-U)⁻¹≤2 := by
    apply (mul_le_mul_iff_right₀ hden).mp
    rw [mul_inv_cancel₀ (ne_of_gt hden)]
    linarith
  have hb : ‖f z-∑i∈Finset.range 3,WP.coeff f i*z^i‖≤2*C :=
    hbound.trans (by nlinarith)
  have he : (∑i∈Finset.range 3,WP.coeff f i*z^i) = WP.coeff f 0+WP.coeff f 1*z+WP.coeff f 2*z^2 := by
    norm_num [Finset.sum_range_succ]
  rw [he] at hb
  convert hb using 1
  dsimp [C]
  ring
end WP.Analysis
