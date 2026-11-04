import Mathlib
/-! Positive scaled-power substitution for actual Mellin integrals.
The identities use the Mathlib Jacobian theorem; no asymptotic or integrability
input is postulated. The integrability equivalence is recorded separately. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory Filter
open scoped Topology
lemma scaled_rpow_image_Ioi (A p ρ : ℝ) (hA : 0<A) (hp : 0<p) (hρ : 0≤ρ) :
    (fun t:ℝ => A*t^p) '' Ioi ρ = Ioi (A*ρ^p) := by
  have him : (fun t:ℝ => t^p) '' Ioi ρ=Ioi (ρ^p) := by
    rw [(Real.continuous_rpow_const hp.le).continuousOn.image_Ioi_of_strictMonoOn
      ((Real.strictMonoOn_rpow_Ici_of_exponent_pos hp).mono (Ici_subset_Ici.mpr hρ))
      (tendsto_rpow_atTop hp)]
  rw [show (fun t:ℝ => A*t^p)=(fun t:ℝ => A*t) ∘ (fun t:ℝ => t^p) by rfl,
    Set.image_comp,him]
  exact (OrderIso.mulLeft₀ A hA).image_Ioi _
lemma integral_scaled_rpow_Ioi {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F:ℝ→E) (A p ρ : ℝ) (hA : 0<A) (hp : 0<p) (hρ : 0≤ρ) :
    (∫ x in Ioi (A*ρ^p),F x)=
      ∫t in Ioi ρ,(A*p*t^(p-1)) • F (A*t^p) := by
  rw [←scaled_rpow_image_Ioi A p ρ hA hp hρ]
  have hd : ∀ t∈Ioi ρ, HasDerivWithinAt (fun t:ℝ=>A*t^p)
      (A*p*t^(p-1)) (Ioi ρ) t := by
    intro t ht
    have ht0 : 0<t := lt_of_le_of_lt hρ ht
    convert ((Real.hasDerivAt_rpow_const (Or.inl ht0.ne')).const_mul A).hasDerivWithinAt using 1 <;> ring
  have hi : InjOn (fun t:ℝ=>A*t^p) (Ioi ρ) := by
    intro x hx y hy hxy
    have he : x^p=y^p := mul_left_cancel₀ hA.ne' hxy
    exact (Real.rpow_left_inj (lt_of_le_of_lt hρ hx).le
      (lt_of_le_of_lt hρ hy).le hp.ne').mp he
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hi F]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hA.le hp.le)
    (Real.rpow_nonneg (hρ.trans (show ρ≤t from ht.le)) _))]
lemma integrable_scaled_rpow_Ioi_iff {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F:ℝ→E) (A p ρ : ℝ) (hA : 0<A) (hp : 0<p) (hρ : 0≤ρ) :
    IntegrableOn F (Ioi (A*ρ^p)) ↔
      IntegrableOn (fun t:ℝ => (A*p*t^(p-1)) • F (A*t^p)) (Ioi ρ) := by
  rw [←scaled_rpow_image_Ioi A p ρ hA hp hρ]
  have hd : ∀ t∈Ioi ρ, HasDerivWithinAt (fun t:ℝ=>A*t^p)
      (A*p*t^(p-1)) (Ioi ρ) t := by
    intro t ht
    have ht0 : 0<t := lt_of_le_of_lt hρ ht
    convert ((Real.hasDerivAt_rpow_const (Or.inl ht0.ne')).const_mul A).hasDerivWithinAt using 1 <;> ring
  have hi : InjOn (fun t:ℝ=>A*t^p) (Ioi ρ) := by
    intro x hx y hy hxy
    have he : x^p=y^p := mul_left_cancel₀ hA.ne' hxy
    exact (Real.rpow_left_inj (lt_of_le_of_lt hρ hx).le
      (lt_of_le_of_lt hρ hy).le hp.ne').mp he
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hi F]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hA.le hp.le)
    (Real.rpow_nonneg (hρ.trans (show ρ≤t from ht.le)) _))]
end WP.Analysis
