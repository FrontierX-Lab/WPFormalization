import WPFormalization.Analysis.BesselZeros
import WPFormalization.Analysis.PositiveRootInfimum
import WPFormalization.Analysis.CriticalBesselData

/-! The explicit series dictionary, retaining the actual Bessel series and
the infimum definitions of their first positive zeros. -/
noncomputable section
namespace WP
open Set

lemma X_eq_sqrt_besselJ1 (z : ℂ) : X z = Complex.sqrt z*besselJ₁ (2*Complex.sqrt z) := by
  unfold X besselJ₁
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2:ℂ) ≠ 0)]
  have hp : Complex.sqrt z*(Complex.sqrt z)^(2*n+1) = z^(n+1) := by
    rw [← pow_succ']
    have he : 2*n+1+1 = 2*(n+1) := by omega
    rw [he,pow_mul,complex_sqrt_sq]
  rw [← hp]
  ring

lemma positive_zero_infimum_root (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 ≠ 0)
    (hs : {x : ℝ | 0 < x ∧ f x = 0}.Nonempty) :
    f (sInf {x : ℝ | 0 < x ∧ f x = 0}) = 0 := by
  have he : {x : ℝ | 0 < x ∧ f x = 0} = Ici 0 ∩ {x : ℝ | f x = 0} := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.le,hx.2⟩
    · intro hx
      refine ⟨lt_of_le_of_ne hx.1 ?_,hx.2⟩
      intro hh
      exact h0 (hh ▸ hx.2)
  have hclosed : IsClosed {x : ℝ | 0 < x ∧ f x = 0} := by
    rw [he]
    exact isClosed_Ici.inter (isClosed_eq hc continuous_const)
  exact (hclosed.csInf_mem hs ⟨0,fun x hx => hx.1.le⟩).2

lemma besselJ0_entire : Differentiable ℂ besselJ₀ := by
  have he : besselJ₀ = fun t : ℂ => deriv X (t^2/4) :=
    funext besselJ0_eq_derivX_square
  rw [he]
  have hd : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  exact hd.comp (by fun_prop)

lemma besselJ0_zero_value : besselJ₀ (0:ℂ) = 1 := by
  rw [besselJ0_eq_derivX_square]
  simpa using iteratedDeriv_X_succ_zero 0

/- Existence follows from the actual X zero obtained by alternating bounds and IVT. -/
lemma besselJ0_positive_zero_from_X : ∃ t : ℝ, 0 < t ∧ besselJ₀ t = 0 := by
  refine ⟨2*Real.sqrt y₀,mul_pos (by norm_num) (Real.sqrt_pos.2 y₀_pos),?_⟩
  rw [besselJ0_eq_derivX_square]
  have he : (((2*Real.sqrt y₀:ℝ):ℂ))^2/4 = (y₀:ℂ) := by
    push_cast
    have hr := congrArg (fun x : ℝ => (x:ℂ)) (Real.sq_sqrt y₀_pos.le)
    push_cast at hr
    linear_combination hr
  rw [he]
  exact derivX_y₀_zero

lemma firstJ0Zero_pos : 0 < firstJ₀Zero := by
  apply Analysis.positive_zero_sInf_pos (fun t : ℝ => besselJ₀ t)
    (besselJ0_entire.continuous.comp Complex.continuous_ofReal).continuousAt
  · simpa only [Complex.ofReal_zero,besselJ0_zero_value] using (one_ne_zero : (1:ℂ) ≠ 0)
  · exact besselJ0_positive_zero_from_X

lemma besselJ0_firstJ0Zero_zero : besselJ₀ (firstJ₀Zero:ℂ) = 0 := by
  apply positive_zero_infimum_root (fun t : ℝ => besselJ₀ t)
    (besselJ0_entire.continuous.comp Complex.continuous_ofReal)
  · simpa only [Complex.ofReal_zero,besselJ0_zero_value] using (one_ne_zero : (1:ℂ) ≠ 0)
  · exact besselJ0_positive_zero_from_X

lemma y₀_eq_firstJ0Zero : y₀ = firstJ₀Zero^2/4 := by
  have hj : besselJ₀ (((2*Real.sqrt y₀:ℝ):ℂ)) = 0 := by
    rw [besselJ0_eq_derivX_square]
    have he : (((2*Real.sqrt y₀:ℝ):ℂ))^2/4 = (y₀:ℂ) := by
      push_cast
      have hr := congrArg (fun x : ℝ => (x:ℂ)) (Real.sq_sqrt y₀_pos.le)
      push_cast at hr
      linear_combination hr
    rw [he]
    exact derivX_y₀_zero
  have ht : firstJ₀Zero ≤ 2*Real.sqrt y₀ := by
    apply csInf_le ⟨0,fun t ht => ht.1.le⟩
    exact ⟨mul_pos (by norm_num) (Real.sqrt_pos.2 y₀_pos),hj⟩
  have hy : y₀ ≤ firstJ₀Zero^2/4 := by
    apply csInf_le ⟨0,fun y hy => hy.1.le⟩
    refine ⟨div_pos (pow_pos firstJ0Zero_pos 2) (by norm_num),?_⟩
    have hh := besselJ0_firstJ0Zero_zero
    rw [besselJ0_eq_derivX_square] at hh
    simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat] using hh
  apply le_antisymm hy
  have hh := mul_self_le_mul_self firstJ0Zero_pos.le ht
  nlinarith only [hh,Real.sq_sqrt y₀_pos.le]

/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: VERIFIED (actual series, alternating bounds and IVT)
-/
@[blueprint "def:bessel"]
theorem bessel_dictionary (z : ℂ) :
    X z = Complex.sqrt z*besselJ₁ (2*Complex.sqrt z) ∧
    deriv X z = besselJ₀ (2*Complex.sqrt z) ∧ y₀ = firstJ₀Zero^2/4 := by
  exact ⟨X_eq_sqrt_besselJ1 z,derivX_eq_besselJ0 z,y₀_eq_firstJ0Zero⟩

namespace External

/- This formerly deferred classical existence statement now has a genuine proof. -/
theorem besselJ0_positive_zero : ∃ t : ℝ, 0 < t ∧ besselJ₀ t = 0 :=
  besselJ0_positive_zero_from_X

end External

end WP
