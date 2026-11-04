import WPFormalization.Analysis.ComplexPrimitiveGluing
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma real_primitive_complex_extension_with_derivative_on_ball (a b : ℝ) (hab : a<b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (Ω : Set ℂ) (q : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q Ω)
    (hdf : ∀ Y∈Ioo a b,HasDerivAt (fun t : ℝ => (f t:ℂ)) (q (Y:ℂ)) Y)
    (x : ℝ) (hx : x∈Icc a b) (r : ℝ) (hr : 0<r) (hsub : Metric.ball (x:ℂ) r⊆Ω) :
    ∃ G : ℂ → ℂ,AnalyticOnNhd ℂ G (Metric.ball (x:ℂ) r) ∧
      (∀z∈Metric.ball (x:ℂ) r,HasDerivAt G (q z) z) ∧
      ∀ Y∈Icc a b,(Y:ℂ)∈Metric.ball (x:ℂ) r → G (Y:ℂ)=(f Y:ℂ) := by
  have hqd : DifferentiableOn ℂ q (Metric.ball (x:ℂ) r) := hq.differentiableOn.mono hsub
  obtain ⟨G,hGx,hGd⟩ := hqd.isExactOn_ball.with_val_at (x:ℂ) (f x:ℂ)
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (x:ℂ) r) :=
    fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G (Metric.ball (x:ℂ) r) := hGdiff.analyticOnNhd Metric.isOpen_ball
  let S : Set ℝ := Ioo a b ∩ Metric.ball x r
  let J : Set ℝ := Icc a b ∩ Metric.ball x r
  have hSopen : IsOpen S := isOpen_Ioo.inter Metric.isOpen_ball
  have hSconn : IsPreconnected S := ((convex_Ioo (𝕜:=ℝ) a b).inter (convex_ball x r)).isPreconnected
  have hSJ : S⊆J := inter_subset_inter_left _ Ioo_subset_Icc_self
  have hJcl : J⊆closure S := by
    intro Y hY
    have hYcl : Y∈closure (Ioo a b) := by rw [closure_Ioo hab.ne];exact hY.1
    rw [mem_closure_iff_nhds] at hYcl ⊢
    intro V hV
    obtain ⟨t,htV,htI⟩ := hYcl (V∩Metric.ball x r) (inter_mem hV (Metric.isOpen_ball.mem_nhds hY.2))
    exact ⟨t,htV.1,htI,htV.2⟩
  let D : ℝ → ℂ := fun Y => G (Y:ℂ)-(f Y:ℂ)
  have hDd (Y : ℝ) (hY : Y∈S) : HasDerivAt D 0 Y := by
    have hYb : (Y:ℂ)∈Metric.ball (x:ℂ) r := by
      simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hY.2
    simpa only [D,Pi.sub_def,sub_self] using (hGd (Y:ℂ) hYb).comp_ofReal.sub (hdf Y hY.1)
  obtain ⟨c,hc⟩ := hSopen.exists_is_const_of_deriv_eq_zero hSconn
    (fun Y hY => (hDd Y hY).differentiableAt.differentiableWithinAt)
    (fun Y hY => (hDd Y hY).deriv)
  have hDc : ContinuousOn D J := by
    apply ContinuousOn.sub
    · intro Y hY
      have hYb : (Y:ℂ)∈Metric.ball (x:ℂ) r := by
        simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hY.2
      exact ((hGa _ hYb).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · exact (Complex.continuous_ofReal.comp_continuousOn hf).mono inter_subset_left
  have he : EqOn D (fun _ => c) J :=
    (show EqOn D (fun _ => c) S from hc).of_subset_closure hDc continuousOn_const hSJ hJcl
  have hxJ : x∈J := ⟨hx,Metric.mem_ball_self hr⟩
  have hc0 : c=0 := by
    have hh := he hxJ
    simpa only [D,hGx,sub_self] using hh.symm
  refine ⟨G,hGa,hGd,?_⟩
  intro Y hY hYb
  have hYr : Y∈Metric.ball x r := by
    simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hYb
  have hh := he ⟨hY,hYr⟩
  simpa only [D,hc0,sub_eq_zero] using hh

end WP.Analysis
