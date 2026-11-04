import WPFormalization.Analysis.UniformTaylorRemainder
/-! One fixed Cauchy ball controls every divided difference of a bounded analytic function vanishing at its center. The bound also covers the center derivative. -/
noncomputable section
namespace WP.Analysis
open Set

lemma dslope_uniform_norm_bound (Ω:Set ℂ)(c:ℂ)(R M:ℝ)(hR:0<R)(hM0:0 ≤ M)
    (hball:Metric.closedBall c R⊆Ω)(f:ℂ→ℂ)(hf:AnalyticOnNhd ℂ f Ω)
    (hzero:f c=0)(hbound:∀z∈Ω,‖f z‖ ≤ M)(z:ℂ)(hz:z∈Ω) :
    ‖dslope f c z‖ ≤ 2*M/R := by
  have hfc:DifferentiableOn ℂ f (Metric.closedBall c R):=
    fun w hw=>(hf w (hball hw)).differentiableAt.differentiableWithinAt
  have hSphere:∀w∈Metric.sphere c R,‖f w‖ ≤ M:=
    fun w hw=>hbound w (hball (Metric.sphere_subset_closedBall hw))
  by_cases he:z=c
  · subst z
    rw[dslope_same]
    have hb:=Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      ((hfc.mono Metric.closure_ball_subset_closedBall).diffContOnCl) hSphere
    exact hb.trans (div_le_div_of_nonneg_right (by linarith) hR.le)
  have hn:0<‖z-c‖:=norm_pos_iff.mpr (sub_ne_zero.mpr he)
  rw[dslope_of_ne f he]
  simp only[slope,hzero,vsub_eq_sub,sub_zero,smul_eq_mul,norm_mul,norm_inv]
  rw[mul_comm,←div_eq_mul_inv]
  by_cases hnear:‖z-c‖ ≤ R/2
  · let F:ℂ→ℂ:=fun w=>f (c+w)
    have hshift(w:ℂ)(hw:w∈Metric.closedBall (0:ℂ) R):c+w∈Metric.closedBall c R:=by
      rw[Metric.mem_closedBall,dist_eq_norm]
      simpa only[add_sub_cancel_left,dist_zero_right] using (Metric.mem_closedBall.mp hw)
    have hF:DifferentiableOn ℂ F (Metric.closedBall 0 R):=by
      intro w hw
      exact ((hf (c+w) (hball (hshift w hw))).differentiableAt.comp w
        (differentiableAt_const c|>.add differentiableAt_id)).differentiableWithinAt
    have hFM:∀w∈Metric.sphere (0:ℂ) R,‖F w‖ ≤ M:=by
      intro w hw
      exact hbound (c+w) (hball (hshift w (Metric.sphere_subset_closedBall hw)))
    have hb:=complex_taylor_remainder_bound F R M hR hM0 hF hFM 1 (z-c) hnear
    have hF0:WP.coeff F 0=0:=by simp[WP.coeff,F,hzero]
    simp only[Finset.sum_range_one,hF0,zero_mul,sub_zero,pow_one] at hb
    have hval:F (z-c)=f z:=by dsimp[F];congr 1;ring
    rw[hval] at hb
    apply (div_le_iff₀ hn).mpr
    apply hb.trans_eq
    ring
  · have hfar:R/2 ≤ ‖z-c‖:=le_of_not_ge hnear
    apply (div_le_iff₀ hn).mpr
    apply (hbound z hz).trans
    have hm:=mul_le_mul_of_nonneg_left hfar (by positivity:0 ≤ 2*M/R)
    have heq:(2*M/R)*(R/2)=M:=by field_simp[hR.ne']
    rwa[heq] at hm

end WP.Analysis
