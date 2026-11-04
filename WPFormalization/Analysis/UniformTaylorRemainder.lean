import WPFormalization.Analysis.QuadraticRemainder

/-! One fixed complex Cauchy circle gives simultaneous Taylor remainder bounds at every truncation order. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma complex_taylor_remainder_bound (f : ℂ→ℂ) (R M : ℝ) (hR : 0<R) (hM0 : 0≤M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hM : ∀z∈Metric.sphere (0:ℂ) R,‖f z‖≤M) (N : ℕ) (z : ℂ) (hz : ‖z‖≤R/2) :
    ‖f z-(∑i∈Finset.range N,WP.coeff f i*z^i)‖ ≤ 2*M*(‖z‖/R)^N := by
  have hs := hasSum_coeff_on_ball f R (hf.mono Metric.ball_subset_closedBall) z (by linarith)
  have htail := (hasSum_nat_add_iff' N).mpr hs
  let U : ℝ := ‖z‖/R
  let C : ℝ := M/R^N*‖z‖^N
  have hU0 : 0≤U := div_nonneg (norm_nonneg _) hR.le
  have hU : U≤1/2 := (div_le_iff₀ hR).mpr (by linarith)
  have hC : 0≤C := by dsimp [C];positivity
  have hgeo := (hasSum_geometric_of_norm_lt_one (show ‖U‖<1 by rw [Real.norm_eq_abs,abs_of_nonneg hU0];linarith)).mul_left C
  have hbound := htail.norm_le_of_bounded hgeo (fun n => by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (M/R^(n+N))*‖z‖^(n+N) :=
        mul_le_mul_of_nonneg_right (coeff_norm_le_circle_bound f R M hR hf hM (n+N)) (by positivity)
      _ = C*U^n := by dsimp [C,U];rw [pow_add,pow_add,div_pow];field_simp)
  have hden : 0<1-U := by linarith
  have hinv : (1-U)⁻¹≤2 := by
    apply (mul_le_mul_iff_right₀ hden).mp
    rw [mul_inv_cancel₀ hden.ne']
    linarith
  have hb := hbound.trans (show C*(1-U)⁻¹≤2*C by nlinarith)
  convert hb using 1
  dsimp [C]
  rw [div_pow]
  ring
end WP.Analysis
