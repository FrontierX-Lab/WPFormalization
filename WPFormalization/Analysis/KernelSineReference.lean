import WPFormalization.Analysis.ComplexCharacteristic

/-! The actual undeformed kernel is the sine reference. Its entire extension,
complete zero classification and simplicity use only Mathlib trigonometry
and the proved kernel identity, without an external zero-count theorem. -/
noncomputable section
namespace WP.Analysis
open Set
def sineReference (t : ℂ) : ℂ := K 0 (t^2/2)
lemma sineReference_differentiable : Differentiable ℂ sineReference := by
  unfold sineReference
  exact (K_differentiable 0).comp (by fun_prop)
lemma sineReference_mul (t : ℂ) : t*sineReference t = Complex.sin t := by
  simpa only [sineReference,K,rootKernel] using rootKernel_sine t
lemma sineReference_zero : sineReference 0 = 1 := by
  simp only [sineReference,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,K_zero,derivX_zero]
lemma sineReference_zero_iff (t : ℂ) : sineReference t = 0 ↔
    ∃ k : ℤ, k ≠ 0 ∧ t = (k:ℂ)*Real.pi := by
  constructor
  · intro ht
    have hsin : Complex.sin t = 0 := by rw [← sineReference_mul,ht,mul_zero]
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hsin
    refine ⟨k,?_,hk⟩
    intro he
    subst k
    simp only [Int.cast_zero,zero_mul] at hk
    rw [hk,sineReference_zero] at ht
    exact one_ne_zero ht
  · rintro ⟨k,hk,rfl⟩
    have hsin : Complex.sin ((k:ℂ)*Real.pi) = 0 :=
      Complex.sin_eq_zero_iff.mpr ⟨k,rfl⟩
    rw [← sineReference_mul] at hsin
    apply (mul_eq_zero.mp hsin).resolve_left
    apply mul_ne_zero
    · exact_mod_cast hk
    · exact_mod_cast Real.pi_ne_zero
lemma sineReference_simple (t : ℂ) (ht : sineReference t = 0) :
    deriv sineReference t ≠ 0 := by
  have hsin : Complex.sin t = 0 := by rw [← sineReference_mul,ht,mul_zero]
  have hd := (hasDerivAt_id t).mul (sineReference_differentiable t).hasDerivAt
  have hfun : (fun z : ℂ=>z*sineReference z) = Complex.sin := by
    funext z
    exact sineReference_mul z
  change HasDerivAt (fun z : ℂ=>z*sineReference z)
    (1*sineReference t+t*deriv sineReference t) t at hd
  rw [hfun] at hd
  have he := hd.unique (Complex.hasDerivAt_sin t)
  simp only [one_mul,ht,zero_add] at he
  intro hz
  rw [hz,mul_zero] at he
  have hh := Complex.sin_sq_add_cos_sq t
  rw [hsin,← he] at hh
  norm_num at hh
end WP.Analysis
