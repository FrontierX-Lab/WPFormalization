import Mathlib

/-! Finite radial/arc contour deformation obtained from Mathlib Cauchy on
log-polar rectangles, with a compact-contour Laplace bound. -/

noncomputable section
namespace WP.Analysis
open Set MeasureTheory Complex
open scoped Interval

def radialSegmentIntegral (f : ℂ → ℂ) (θ a b : ℝ) : ℂ :=
  ∫ t in a..b,Complex.exp ((θ:ℂ)*Complex.I)*
    f ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))

def polarArcIntegral (f : ℂ → ℂ) (r θ ψ : ℝ) : ℂ :=
  Complex.I*(∫ y in θ..ψ,(r:ℂ)*Complex.exp ((y:ℂ)*Complex.I)*
    f ((r:ℂ)*Complex.exp ((y:ℂ)*Complex.I)))

lemma exp_polar_horizontal_integral (f : ℂ → ℂ) (u v θ : ℝ) :
    (∫ x in u..v,Complex.exp ((x:ℂ)+(θ:ℂ)*Complex.I)*
      f (Complex.exp ((x:ℂ)+(θ:ℂ)*Complex.I))) =
      radialSegmentIntegral f θ (Real.exp u) (Real.exp v) := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f:=Real.exp) (f':=Real.exp)
    (g:=fun t:ℝ => Complex.exp ((θ:ℂ)*Complex.I)*
      f ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))
    (a:=u) (b:=v) Real.continuous_exp.continuousOn
    (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
  unfold radialSegmentIntegral
  rw [←h]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [Complex.exp_add,←Complex.ofReal_exp]
  simp only [Function.comp_apply,Complex.real_smul]
  ring

lemma polar_rectangle_deformation (f : ℂ → ℂ) (u v θ ψ : ℝ)
    (hf : DifferentiableOn ℂ f
      (Complex.exp '' (Complex.Rectangle ((u : ℂ) + (θ : ℂ) * Complex.I)
        ((v : ℂ) + (ψ : ℂ) * Complex.I)))) :
    radialSegmentIntegral f θ (Real.exp u) (Real.exp v)-
      radialSegmentIntegral f ψ (Real.exp u) (Real.exp v)+
      polarArcIntegral f (Real.exp v) θ ψ-
      polarArcIntegral f (Real.exp u) θ ψ=0 := by
  let F : ℂ → ℂ := fun z => Complex.exp z*f (Complex.exp z)
  have hF : DifferentiableOn ℂ F
      (Complex.Rectangle ((u : ℂ) + (θ : ℂ) * Complex.I) ((v : ℂ) + (ψ : ℂ) * Complex.I)) :=
    Complex.differentiable_exp.differentiableOn.mul
      (hf.comp Complex.differentiable_exp.differentiableOn (mapsTo_image _ _))
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((u : ℂ) + (θ : ℂ) * Complex.I) ((v : ℂ) + (ψ : ℂ) * Complex.I) hF
  have hexp (x y : ℝ) : Complex.exp ((x:ℂ)+(y:ℂ)*Complex.I)=
      (Real.exp x:ℂ)*Complex.exp ((y:ℂ)*Complex.I) := by
    rw [Complex.exp_add,Complex.ofReal_exp]
  have hh (y : ℝ) : (∫ x in u..v,F ((x:ℂ)+(y:ℂ)*Complex.I))=
      radialSegmentIntegral f y (Real.exp u) (Real.exp v) :=
    exp_polar_horizontal_integral f u v y
  have hv (x : ℝ) : Complex.I • (∫ y in θ..ψ,F ((x:ℂ)+(y:ℂ)*Complex.I))=
      polarArcIntegral f (Real.exp x) θ ψ := by
    simp only [polarArcIntegral,F,hexp,smul_eq_mul]
  have hs : (∫ x in u..v,F ((x:ℂ)+(θ:ℂ)*Complex.I))-
      (∫ x in u..v,F ((x:ℂ)+(ψ:ℂ)*Complex.I))+
      Complex.I • (∫ y in θ..ψ,F ((v:ℂ)+(y:ℂ)*Complex.I))-
      Complex.I • (∫ y in θ..ψ,F ((u:ℂ)+(y:ℂ)*Complex.I))=0 := by
    simpa using h
  simpa only [hh,hv] using hs

lemma compact_contour_laplace_norm_bound (H γ δ : ℝ → ℂ) (a b ξ c V M : ℝ)
    (hξ : 0 ≤ ξ) (hV : 0 ≤ V) (_hM : 0 ≤ M)
    (hre : ∀ t ∈ uIcc a b, c ≤ (γ t).re)
    (hδ : ∀ t ∈ uIcc a b, ‖δ t‖ ≤ V) (hH : ∀ t ∈ uIcc a b, ‖H t‖ ≤ M) :
    ‖∫ t in a..b,δ t*Complex.exp (-(ξ:ℂ)*γ t)*H t‖ ≤
      (V*Real.exp (-(ξ*c))*M)*|b-a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  have ht' : t∈uIcc a b := uIoc_subset_uIcc ht
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have hexp : (-(ξ:ℂ)*γ t).re = -(ξ*(γ t).re) := by simp
  rw [hexp]
  apply mul_le_mul
  · apply mul_le_mul
    · exact hδ t ht'
    · apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (hre t ht') hξ
      linarith
    · positivity
    · exact hV
  · exact hH t ht'
  · positivity
  · positivity
end WP.Analysis
