import WPFormalization.Statements.Kernels
/-! Joint kernel derivative continuity and parameter-uniform linear remainder bounds.
These analytic estimates use only the defining integrals and proved X derivatives. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter
open scoped Topology
lemma kernelIntegral_continuous_joint (q : ℝ → ℂ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Continuous g) :
    Continuous (fun p : ℂ × ℂ => ∫ s : ℝ in (0)..1,
      q s*g (p.1+p.2/2*(1-(s : ℂ)^2))) := by
  have hc : Continuous (fun p : (ℂ × ℂ) × ℝ =>
      q p.2*g (p.1.1+p.1.2/2*(1-(p.2 : ℂ)^2))) := by fun_prop
  have h := continuous_parametric_integral_of_continuous (X := ℂ × ℂ) (Y := ℝ) (E := ℂ)
    (f := fun p s => q s*g (p.1+p.2/2*(1-(s : ℂ)^2))) (μ := volume) hc (s := Set.Icc (0 : ℝ) 1) isCompact_Icc
  convert h using 1
  ext p
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
lemma K_joint_deriv_continuous : Continuous (fun p : ℂ × ℂ => deriv (K p.1) p.2) := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have hgc : Continuous (deriv (deriv X)) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using
      (iteratedDeriv_X_differentiable 2).continuous
  have he (Y z : ℂ) : deriv (K Y) z = ∫ s : ℝ in (0)..1,
      ((1-(s : ℂ)^2)/2)*deriv (deriv X) (Y+z/2*(1-(s : ℂ)^2)) := by
    have heq : K Y = fun w => ∫ s : ℝ in (0)..1, (1 : ℂ)*deriv X (Y+w/2*(1-(s : ℂ)^2)) := by
      funext w
      simp only [K,one_mul]
    rw [heq]
    simpa only [one_mul] using
      (hasDerivAt_kernelIntegral (fun _ => 1) continuous_const (deriv X) hg Y z).deriv
  have heq : (fun p : ℂ × ℂ => deriv (K p.1) p.2) =
      fun p => ∫ s : ℝ in (0)..1, ((1-(s : ℂ)^2)/2)*
        deriv (deriv X) (p.1+p.2/2*(1-(s : ℂ)^2)) := funext (fun p => he p.1 p.2)
  rw [heq]
  exact kernelIntegral_continuous_joint _ (by fun_prop) _ hgc
lemma H_joint_deriv_continuous : Continuous (fun p : ℂ × ℂ => deriv (H p.1) p.2) := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have hgc : Continuous (deriv (deriv X)) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using
      (iteratedDeriv_X_differentiable 2).continuous
  have he (Y z : ℂ) : deriv (H Y) z = 3*∫ s : ℝ in (0)..1,
      ((s : ℂ)^2*(1-(s : ℂ)^2)/2)*deriv (deriv X) (Y+z/2*(1-(s : ℂ)^2)) := by
    exact ((hasDerivAt_kernelIntegral (fun s : ℝ => (s : ℂ)^2) (by fun_prop)
      (deriv X) hg Y z).const_mul (3 : ℂ)).deriv
  have heq : (fun p : ℂ × ℂ => deriv (H p.1) p.2) =
      fun p => 3*∫ s : ℝ in (0)..1, ((s : ℂ)^2*(1-(s : ℂ)^2)/2)*
        deriv (deriv X) (p.1+p.2/2*(1-(s : ℂ)^2)) := funext (fun p => he p.1 p.2)
  rw [heq]
  exact continuous_const.mul (kernelIntegral_continuous_joint _ (by fun_prop) _ hgc)
lemma family_first_order_uniform (F : ℂ → ℂ → ℂ)
    (hF : ∀ Y, Differentiable ℂ (F Y))
    (hD : Continuous (fun p : ℂ × ℂ => deriv (F p.1) p.2)) (Y₀ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y z : ℂ, ‖Y-Y₀‖ < δ → ‖z‖ < δ →
      ‖F Y z-F Y 0-deriv (F Y₀) 0*z‖ ≤ ε*‖z‖ := by
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp (hD.continuousAt (x := (Y₀,0))) ε hε
  refine ⟨δ,hδ,?_⟩
  intro Y z hY hz
  let d := deriv (F Y₀) 0
  let f (w : ℂ) := F Y w-F Y 0-d*w
  have heq : f = ((fun w => F Y w-F Y 0)-(fun w => d*w)) := rfl
  have hasD (w : ℂ) : HasDerivAt f (deriv (F Y) w-d) w := by
    rw [heq]
    simpa only [id_eq,mul_one] using
      ((((hF Y w).hasDerivAt).sub_const (F Y 0)).sub ((hasDerivAt_id w).const_mul d))
  have hf (w : ℂ) : DifferentiableAt ℂ f w := (hasD w).differentiableAt
  have hd (w : ℂ) : deriv f w = deriv (F Y) w-d := (hasD w).deriv
  have hb (w : ℂ) (hw : w ∈ Metric.ball 0 δ) : ‖deriv f w‖ ≤ ε := by
    rw [hd]
    have hp : dist (Y,w) (Y₀,(0 : ℂ)) < δ := by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨by simpa only [dist_eq_norm] using hY,by simpa using hw⟩
    exact (show ‖deriv (F Y) w-d‖ < ε by simpa only [dist_eq_norm] using hbound hp).le
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (s := Metric.ball 0 δ) (x := (0 : ℂ)) (y := z)
    (fun w hw => hf w) hb (convex_ball (0 : ℂ) δ)
      (by simpa using hδ) (by simpa using hz)
  simpa only [f,mul_zero,sub_self,sub_zero] using h

lemma K_first_order_uniform (Y₀ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y z : ℂ, ‖Y-Y₀‖ < δ → ‖z‖ < δ →
      ‖K Y z-deriv X Y-(iteratedDeriv 2 X Y₀/3)*z‖ ≤ ε*‖z‖ := by
  obtain ⟨δ,hδ,h⟩ := family_first_order_uniform K K_differentiable K_joint_deriv_continuous Y₀ ε hε
  have hd : deriv (K Y₀) 0 = iteratedDeriv 2 X Y₀/3 := by
    have hd := iteratedDeriv_K_zero Y₀ 1
    norm_num [oddFactorial,Finset.prod_range_succ] at hd
    convert hd using 1 <;> ring
  refine ⟨δ,hδ,?_⟩
  intro Y z hY hz
  simpa only [K_zero,hd] using h Y z hY hz
lemma H_first_order_uniform (Y₀ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y z : ℂ, ‖Y-Y₀‖ < δ → ‖z‖ < δ →
      ‖H Y z-deriv X Y-(iteratedDeriv 2 X Y₀/5)*z‖ ≤ ε*‖z‖ := by
  obtain ⟨δ,hδ,h⟩ := family_first_order_uniform H H_differentiable H_joint_deriv_continuous Y₀ ε hε
  have hd : deriv (H Y₀) 0 = iteratedDeriv 2 X Y₀/5 := by
    have hd := iteratedDeriv_H_zero Y₀ 1
    norm_num [oddFactorial,Finset.prod_range_succ] at hd
    convert hd using 1 <;> ring
  refine ⟨δ,hδ,?_⟩
  intro Y z hY hz
  simpa only [H_zero,hd] using h Y z hY hz
end WP.Analysis
