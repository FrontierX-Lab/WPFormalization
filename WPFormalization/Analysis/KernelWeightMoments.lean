import WPFormalization.Analysis.KernelMomentBounds

/-! The total mass and first moment of the actual canonical kernel weights.
Taylor convergence on the common disk permits evaluation at one. Two
derivatives of the removable first-root factor then identify both moments
with derivatives of the original normalized kernel. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology

lemma weight_hasSum_at_one (Y:ℝ) (hY:Y∈Icc 0 y₀) :
    HasSum (weight Y) (weightGenerating Y 1).re := by
  obtain ⟨R,M,hR,hM,hdata⟩:=weightGenerating_uniform_analytic
  have hs:=hasSum_coeff_on_ball (weightGenerating Y) R
    ((hdata Y hY).1.mono Metric.ball_subset_closedBall) 1 (by simpa using hR)
  convert Complex.hasSum_re hs using 1
  ext n
  rw [one_pow,mul_one]
  exact (weightGenerating_coeff Y hY n).symm

lemma weight_first_moment_hasSum_at_one (Y:ℝ) (hY:Y∈Icc 0 y₀) :
    HasSum (fun n:ℕ=>(n:ℝ)*weight Y n) (deriv (weightGenerating Y) 1).re := by
  obtain ⟨R,M,hR,hM,hdata⟩:=weightGenerating_uniform_analytic
  have hf:=((hdata Y hY).1.mono Metric.ball_subset_closedBall)
  have hA (z:ℂ)(hz:z∈Metric.ball 0 R):AnalyticAt ℂ (weightGenerating Y) z:=
    hf.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hz0:(0:ℂ)∈Metric.ball 0 R:=by simp only [Metric.mem_ball,dist_self];linarith
  have hD:DifferentiableOn ℂ (fun z=>z*deriv (weightGenerating Y) z) (Metric.ball 0 R):=by
    intro z hz
    exact (differentiableAt_id.mul (hA z hz).deriv.differentiableAt).differentiableWithinAt
  have hs:=hasSum_coeff_on_ball _ R hD 1 (by simpa using hR)
  rw [one_mul] at hs
  convert Complex.hasSum_re hs using 1
  ext n
  rw [one_pow,mul_one,harmonic_coeff_euler _ (hA 0 hz0) n]
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  rw [←weightGenerating_coeff Y hY n]
  rfl

lemma barK_deriv_deflated (Y:ℝ) (hY:Y∈Icc 0 y₀) (w:ℂ):
    deriv (barK Y) w = -deflatedBarK Y w+(1-w)*deriv (deflatedBarK Y) w := by
  have hd:=((hasDerivAt_id w).const_sub 1).mul
    ((deflatedBarK_differentiable Y w).hasDerivAt)
  have he:(fun z:ℂ=>(1-z)*deflatedBarK Y z)=barK Y:=
    funext (deflatedBarK_identity Y hY)
  change HasDerivAt (fun z:ℂ=>(1-z)*deflatedBarK Y z) _ w at hd
  rw [he] at hd
  simpa only [id_eq,neg_one_mul] using hd.deriv

lemma deflatedBarK_deriv_one (Y:ℝ) (hY:Y∈Icc 0 y₀):
    deriv (deflatedBarK Y) 1 = -(iteratedDeriv 2 (barK Y) 1)/2 := by
  have hB:=deflatedBarK_differentiable Y
  have hd:=((hB 1).hasDerivAt.neg).add
    (((hasDerivAt_id (1:ℂ)).const_sub 1).mul ((hB.deriv 1).hasDerivAt))
  have he:(fun z:ℂ=>-deflatedBarK Y z+(1-z)*deriv (deflatedBarK Y) z)=deriv (barK Y):=
    funext (fun z=>(barK_deriv_deflated Y hY z).symm)
  change HasDerivAt (fun z:ℂ=>-deflatedBarK Y z+(1-z)*deriv (deflatedBarK Y) z) _ 1 at hd
  rw [he] at hd
  have hh:=hd.deriv
  simp only [id_eq,sub_self,zero_mul,add_zero,neg_one_mul] at hh
  have hi:iteratedDeriv 2 (barK Y) 1=deriv (deriv (barK Y)) 1:=by
    simp only [show 2=Nat.succ (Nat.succ 0) from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hi]
  linear_combination (1/2:ℂ)*hh

lemma barK_deriv_one_real (Y:ℝ):(deriv (barK Y) 1).im=0 := by
  simpa only [Complex.ofReal_one] using entire_ofReal_im_zero_of_realCoefficients
    (deriv (barK Y)) ((barK_differentiable Y).deriv)
    (realCoefficients_deriv (barK_realCoefficients Y)) 1

lemma theta_sum_kernel_deriv (Y:ℝ) (hY:Y∈Icc 0 y₀):
    (∑'n:ℕ,weight Y n) = -1/(deriv (barK Y) 1).re := by
  rw [(weight_hasSum_at_one Y hY).tsum_eq]
  have hr:deriv (barK Y) 1=((deriv (barK Y) 1).re:ℂ):=by
    apply Complex.ext <;> simp [barK_deriv_one_real]
  rw [weightGenerating,deflatedBarK_one,hr]
  rw [←Complex.ofReal_neg,←Complex.ofReal_inv,Complex.ofReal_re]
  simp only [inv_neg,neg_div,one_div,Complex.ofReal_re]

lemma first_weight_moment_kernel_deriv (Y:ℝ) (hY:Y∈Icc 0 y₀):
    (∑'n:ℕ,(n:ℝ)*weight Y n) = (iteratedDeriv 2 (barK Y) 1).re/(2*(deriv (barK Y) 1).re^2) := by
  rw [(weight_first_moment_hasSum_at_one Y hY).tsum_eq]
  have hn:deflatedBarK Y 1≠0:=deflatedBarK_zero_free_unit Y hY 1 (by norm_num)
  have hd:=((deflatedBarK_differentiable Y 1).hasDerivAt.inv hn).deriv
  change deriv (fun z:ℂ=>(deflatedBarK Y z)⁻¹) 1 = _ at hd
  change (deriv (fun z:ℂ=>(deflatedBarK Y z)⁻¹) 1).re = _
  rw [hd,deflatedBarK_deriv_one Y hY,deflatedBarK_one]
  have hr:deriv (barK Y) 1=((deriv (barK Y) 1).re:ℂ):=by
    apply Complex.ext <;> simp [barK_deriv_one_real]
  have hc: -( -(iteratedDeriv 2 (barK Y) 1)/2)/(-deriv (barK Y) 1)^2 =
      (iteratedDeriv 2 (barK Y) 1)/(2*(deriv (barK Y) 1)^2):=by ring
  rw [hc,hr]
  simp only [←Complex.ofReal_pow,←Complex.ofReal_ofNat,←Complex.ofReal_mul,Complex.div_ofReal_re,Complex.ofReal_re]
end WP.Analysis
