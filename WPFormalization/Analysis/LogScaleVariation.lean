import Mathlib
/-! An exact variation bound controlled by a decreasing logarithmic scale.
Monotonicity of f ± k*z follows from the derivative bound; no integral
representation or unproved analytic input is needed. -/
noncomputable section
open Set
namespace WP.Analysis
lemma log_scale_variation_bound (f z : ℝ → ℝ) (a b k : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hfd : ∀ x ∈ Ioo a b,DifferentiableAt ℝ f x)
    (hzd : ∀ x ∈ Ioo a b,DifferentiableAt ℝ z x)
    (he : ∀ x ∈ Ioo a b,|deriv f x| ≤ k*(-deriv z x)) :
    |f b-f a| ≤ k*(z a-z b) := by
  have hp : AntitoneOn (fun x => f x+k*z x) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (hf.add (hz.const_mul k))
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hfd x hx).add ((hzd x hx).const_mul k)).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [((hfd x hx).hasDerivAt.add ((hzd x hx).hasDerivAt.const_mul k)).deriv]
      linarith [he x hx,le_abs_self (deriv f x)]
  have hm : MonotoneOn (fun x => f x-k*z x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hf.sub (hz.const_mul k))
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hfd x hx).sub ((hzd x hx).const_mul k)).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [((hfd x hx).hasDerivAt.sub ((hzd x hx).hasDerivAt.const_mul k)).deriv]
      linarith [he x hx,neg_abs_le (deriv f x)]
  have hplus := hp ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have hminus := hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  apply abs_le.mpr
  constructor <;> dsimp only at hplus hminus <;> linarith
end WP.Analysis
