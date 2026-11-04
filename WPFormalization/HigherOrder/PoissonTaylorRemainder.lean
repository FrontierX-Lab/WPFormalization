import WPFormalization.HigherOrder.PoissonCoefficientOperator
import WPFormalization.Analysis.UniformTaylorRemainder
noncomputable section
namespace WP.HigherOrder
open scoped Topology

def poissonTaylorPolynomial (f : ℂ → ℂ) (ν : ℂ) (N : ℕ) (u : ℂ) : ℂ :=
  ∑m∈Finset.range N,WP.coeff (fun z=>f (ν+z)) m*(u-ν)^m

lemma poissonTaylorPolynomial_analytic (f : ℂ → ℂ) (ν : ℂ) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (poissonTaylorPolynomial f ν N) z := by
  unfold poissonTaylorPolynomial
  apply Finset.analyticAt_fun_sum
  intro m hm
  fun_prop

lemma poissonCoefficientOperator_taylor (h : ℝ) (hh : h≠0) (k N : ℕ) (f : ℂ → ℂ) :
    poissonCoefficientOperator h k (poissonTaylorPolynomial f ((k:ℂ)/(h:ℂ)) N)=
      ∑m∈Finset.range N,WP.coeff (fun z=>f ((k:ℂ)/(h:ℂ)+z)) m*
        ((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)/(h:ℂ)^m) := by
  exact poissonCoefficientOperator_centered_polynomial h hh k (Finset.range N) _

lemma poissonTaylorRemainder_circle_bound (R M ν : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hν0 : 0 ≤ ν) (hν : ν ≤ R/8) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hb : ∀z∈Metric.closedBall (0:ℂ) R,‖f z‖ ≤ M) (N : ℕ) (θ : ℝ) :
    ‖f ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-
      poissonTaylorPolynomial f (ν:ℂ) (2*N) ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖ ≤
        (2*M*(2*ν/R)^(2*N))*θ^(2*N) := by
  let g : ℂ → ℂ := fun z=>f ((ν:ℂ)+z)
  let w : ℂ := (ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)-(ν:ℂ)
  have hnorm (z : ℂ) (hz : z∈Metric.closedBall (0:ℂ) (R/2)) :
      (ν:ℂ)+z∈Metric.closedBall (0:ℂ) R := by
    have hzn : ‖z‖ ≤ R/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have ht := norm_add_le (ν:ℂ) z
    rw [Complex.norm_of_nonneg hν0] at ht
    linarith
  have hg : DifferentiableOn ℂ g (Metric.closedBall 0 (R/2)) := by
    intro z hz
    exact ((hf _ (hnorm z hz)).differentiableAt.comp z (by fun_prop)).differentiableWithinAt
  have hgM (z : ℂ) (hz : z∈Metric.sphere (0:ℂ) (R/2)) : ‖g z‖ ≤ M :=
    hb _ (hnorm z (Metric.sphere_subset_closedBall hz))
  have hw2 : ‖w‖ ≤ 2*ν := by
    dsimp only [w]
    have he : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := Complex.norm_exp_ofReal_mul_I θ
    have ht := norm_sub_le ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) (ν:ℂ)
    rw [norm_mul,he,mul_one,Complex.norm_of_nonneg hν0] at ht
    linarith
  have hwθ : ‖w‖ ≤ ν*|θ| := by
    have he : w=(ν:ℂ)*(Complex.exp (Complex.I*(θ:ℂ))-1) := by dsimp [w];rw [mul_comm Complex.I (θ:ℂ)];ring
    rw [he,norm_mul,Complex.norm_of_nonneg hν0]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=θ))) hν0
  have ht := Analysis.complex_taylor_remainder_bound g (R/2) M (half_pos hR) hM hg hgM (2*N) w (by linarith)
  have heval : (ν:ℂ)+w=(ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) := by dsimp [w];ring
  have hleft : g w-(∑i∈Finset.range (2*N),WP.coeff g i*w^i)=
      f ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-
        poissonTaylorPolynomial f (ν:ℂ) (2*N) ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) := by
    simp only [g,heval,poissonTaylorPolynomial,w]
  rw [hleft] at ht
  calc _ ≤ 2*M*(‖w‖/(R/2))^(2*N) := ht
       _ ≤ 2*M*((ν*|θ|)/(R/2))^(2*N) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
            (div_le_div_of_nonneg_right hwθ (by positivity)) _) (by positivity)
       _ = _ := by
        have ha : |θ|^(2*N)=θ^(2*N) := by simp only [pow_mul,sq_abs]
        rw [show ν*|θ|/(R/2)=(2*ν/R)*|θ| by ring,mul_pow,ha]
        ring
end WP.HigherOrder
