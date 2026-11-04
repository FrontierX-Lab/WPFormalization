import Mathlib
/-! Elementary inverse-parameter and logarithmic increment bounds for the original degree saddle. -/
set_option autoImplicit false
noncomputable section
namespace WP.Analysis
open Set

lemma inverse_parameter_ordered_lipschitz (F Z:ℝ→ℝ)(R U a:ℝ)(ha:0 < a)
    (hF:∀x∈Icc (0:ℝ) R,DifferentiableAt ℝ F x)
    (hmono:StrictMonoOn F (Icc (0:ℝ) R))
    (hlower:∀x∈Icc (0:ℝ) R,a ≤ deriv F x)
    (hinv:∀u∈Icc (0:ℝ) U,Z u∈Icc (0:ℝ) R∧F (Z u)=u)
    (u v:ℝ)(hu:u∈Icc (0:ℝ) U)(hv:v∈Icc (0:ℝ) U)(huv:u ≤ v):
    0 ≤ Z v-Z u∧Z v-Z u ≤ (v-u)/a:=by
  have hzu:=hinv u hu
  have hzv:=hinv v hv
  have horder:Z u ≤ Z v:=(hmono.le_iff_le hzu.1 hzv.1).mp (by simpa only[hzu.2,hzv.2] using huv)
  have hb: a*(Z v-Z u) ≤ v-u:=by
    have H:=(convex_Icc (0:ℝ) R).mul_sub_le_image_sub_of_le_deriv
      (fun x hx=> (hF x hx).continuousAt.continuousWithinAt)
      (fun x hx=> (hF x (interior_subset hx)).differentiableWithinAt)
      (fun x hx=> hlower x (interior_subset hx)) (Z u) hzu.1 (Z v) hzv.1 horder
    simpa only[hzu.2,hzv.2] using H
  exact ⟨sub_nonneg.mpr horder,(le_div_iff₀ ha).mpr (by nlinarith only[hb])⟩

lemma log_ordered_difference_le (a b:ℝ)(ha:0 < a)(hab:a ≤ b):
    0 ≤ Real.log b-Real.log a∧Real.log b-Real.log a ≤ (b-a)/a:=by
  have hb:0 < b:=ha.trans_le hab
  refine ⟨sub_nonneg.mpr (Real.log_le_log ha hab),?_⟩
  have H:=Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw[Real.log_div hb.ne' ha.ne'] at H
  convert H using 1  <;> field_simp  <;> ring

lemma real_log_action_ordered_difference (f:ℝ→ℝ)(R C:ℝ)
    (hf:∀x∈Icc (0:ℝ) R,DifferentiableAt ℝ f x)
    (hdf:∀x∈Icc (0:ℝ) R,0 ≤ deriv f x∧deriv f x ≤ C)
    (x y:ℝ)(hx:x∈Icc (0:ℝ) R)(hy:y∈Icc (0:ℝ) R)(hxy:x ≤ y):
    0 ≤ f y-f x∧f y-f x ≤ C*(y-x):=by
  have hc:ContinuousOn f (Icc (0:ℝ) R):=fun z hz=> (hf z hz).continuousAt.continuousWithinAt
  have hd:DifferentiableOn ℝ f (interior (Icc (0:ℝ) R)):=fun z hz=> (hf z (interior_subset hz)).differentiableWithinAt
  have hlo:=(convex_Icc (0:ℝ) R).mul_sub_le_image_sub_of_le_deriv hc hd
    (fun z hz=> (hdf z (interior_subset hz)).1) x hx y hy hxy
  have hup:=(convex_Icc (0:ℝ) R).image_sub_le_mul_sub_of_deriv_le hc hd
    (fun z hz=> (hdf z (interior_subset hz)).2) x hx y hy hxy
  simpa only[zero_mul] using And.intro hlo hup
end WP.Analysis
