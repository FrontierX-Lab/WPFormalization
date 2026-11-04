import Mathlib

/-! Generic Laplace remainder estimates, uniform in the Taylor order.

The local remainder and the retained-polynomial extension are controlled by
Gamma moments. The outer exponential error has the same factorial scale.
These are proved analytic inequalities; no Painleve object or jump estimate
is assumed.
-/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set

lemma watson_gamma_add_nat_bound (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (L : ℕ) :
    Real.Gamma (s+(L:ℝ)) ≤ Real.Gamma s*(L.factorial:ℝ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.cast_add,Nat.cast_one,←add_assoc,
      Real.Gamma_add_one (by positivity : s+(L:ℝ) ≠ 0),Nat.factorial_succ,Nat.cast_mul]
    calc
      _ ≤ ((L:ℝ)+1)*(Real.Gamma s*(L.factorial:ℝ)) := by
        apply mul_le_mul
        · linarith
        · exact ih
        · exact (Real.Gamma_pos_of_pos (by positivity : 0 < s+(L:ℝ))).le
        · positivity
      _ = _ := by push_cast;ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma laplace_power_remainder_bound (R : ℝ → E) (T : Set ℝ)
    (hT : MeasurableSet T) (hT0 : T ⊆ Ioi 0) (s ξ K : ℝ) (L : ℕ)
    (hs : 0 < s) (hξ : 0 < ξ) (hK : 0 ≤ K)
    (hR : AEStronglyMeasurable R (volume.restrict T))
    (hbound : ∀ t ∈ T, ‖R t‖ ≤ K * t ^ L) :
    IntegrableOn (fun t : ℝ => (Real.exp (-(ξ*t))*t^(s-1)) • R t) T ∧
      ‖∫ t in T, (Real.exp (-(ξ*t))*t^(s-1)) • R t‖ ≤
        K*((1/ξ)^(s+(L:ℝ))*Real.Gamma (s+(L:ℝ))) := by
  have hsL : 0 < s+(L:ℝ) := by positivity
  have hmaj0 : IntegrableOn (fun t:ℝ => t^(s+(L:ℝ)-1)*Real.exp (-(ξ*t))) (Ioi 0) := by
    simpa only [Real.rpow_one,neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=s+(L:ℝ)-1)
        (b:=ξ) (by linarith) (by norm_num) hξ)
  have hmaj : IntegrableOn (fun t:ℝ => K*(t^(s+(L:ℝ)-1)*Real.exp (-(ξ*t)))) T :=
    (hmaj0.mono_set hT0).const_mul K
  have hp (t : ℝ) (ht : t ∈ T) :
      ‖(Real.exp (-(ξ*t))*t^(s-1)) • R t‖ ≤
        K*(t^(s+(L:ℝ)-1)*Real.exp (-(ξ*t))) := by
    have ht0 : 0 < t := hT0 ht
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.exp (-(ξ*t))*t^(s-1))*(K*t^L) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)
      _ = _ := by
        have he : t^(s-1)*t^L=t^(s+(L:ℝ)-1) := by
          rw [←Real.rpow_natCast,←Real.rpow_add ht0]
          congr 1
          ring
        calc
          _ = K*(t^(s-1)*t^L)*Real.exp (-(ξ*t)) := by ring
          _ = _ := by rw [he];ring
  have hf : AEStronglyMeasurable (fun t:ℝ => (Real.exp (-(ξ*t))*t^(s-1)) • R t)
      (volume.restrict T) :=
    (by fun_prop : Measurable (fun t:ℝ => Real.exp (-(ξ*t))*t^(s-1))).aestronglyMeasurable.smul hR
  have hi := hmaj.mono' hf (ae_restrict_of_forall_mem hT hp)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t in T, ‖(Real.exp (-(ξ*t))*t^(s-1)) • R t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in T, K*(t^(s+(L:ℝ)-1)*Real.exp (-(ξ*t))) :=
      integral_mono_ae hi.norm hmaj (ae_restrict_of_forall_mem hT hp)
    _ = K*(∫ t in T,t^(s+(L:ℝ)-1)*Real.exp (-(ξ*t))) := integral_const_mul _ _
    _ ≤ K*(∫ t in Ioi 0,t^(s+(L:ℝ)-1)*Real.exp (-(ξ*t))) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply setIntegral_mono_set hmaj0
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        positivity
      · exact Filter.Eventually.of_forall hT0
    _ = _ := by rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hsL hξ]

lemma normalized_laplace_remainder_factorial_bound (R : ℝ → E) (T : Set ℝ)
    (hT : MeasurableSet T) (hT0 : T ⊆ Ioi 0) (s ξ K : ℝ) (L : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hξ : 0 < ξ) (hK : 0 ≤ K)
    (hR : AEStronglyMeasurable R (volume.restrict T))
    (hbound : ∀ t ∈ T, ‖R t‖ ≤ K * t ^ L) :
    ξ^s*‖∫ t in T,(Real.exp (-(ξ*t))*t^(s-1)) • R t‖ ≤
      K*Real.Gamma s*(L.factorial:ℝ)/ξ^L := by
  have hb := (laplace_power_remainder_bound R T hT hT0 s ξ K L hs hξ hK hR hbound).2
  have hpow : ξ^s*(1/ξ)^(s+(L:ℝ))=1/ξ^L := by
    rw [one_div,Real.inv_rpow hξ.le,Real.rpow_add hξ,Real.rpow_natCast]
    have hx : ξ^s ≠ 0 := (Real.rpow_pos_of_pos hξ s).ne'
    field_simp
  calc
    _ ≤ ξ^s*(K*((1/ξ)^(s+(L:ℝ))*Real.Gamma (s+(L:ℝ)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = K*Real.Gamma (s+(L:ℝ))/ξ^L := by
      calc
        _ = K*Real.Gamma (s+(L:ℝ))*(ξ^s*(1/ξ)^(s+(L:ℝ))) := by ring
        _ = _ := by rw [hpow];ring
    _ ≤ _ := by
      simpa only [mul_assoc] using div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (watson_gamma_add_nat_bound s hs hs1 L) hK)
        (by positivity : 0 ≤ ξ^L)

lemma finite_polynomial_tail_pointwise_bound (c : ℕ → E) (M r t : ℝ)
    (hM : 0 ≤ M) (hr : 0 < r) (ht : r ≤ t)
    (hc : ∀ j : ℕ, ‖c j‖ ≤ M/r^j) (L : ℕ) :
    ‖∑ j ∈ Finset.range L, t^j • c j‖ ≤ (M*(2/r)^L)*t^L := by
  have ht0 : 0 < t := hr.trans_le ht
  have hrat : 1 ≤ t/r := (le_div_iff₀ hr).2 (by simpa)
  have hp (j : ℕ) (hj : j∈Finset.range L) :
      ‖t^j • c j‖ ≤ M*(t/r)^L := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht0.le _)]
    calc
      _ ≤ t^j*(M/r^j) := mul_le_mul_of_nonneg_left (hc j) (by positivity)
      _ = M*(t/r)^j := by rw [div_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hrat (Finset.mem_range.mp hj).le) hM
  calc
    _ ≤ ∑ j ∈ Finset.range L, ‖t^j • c j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range L, M*(t/r)^L := Finset.sum_le_sum hp
    _ = (L:ℝ)*(M*(t/r)^L) := by simp
    _ ≤ (2:ℝ)^L*(M*(t/r)^L) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show L ≤ (2:ℕ)^L from Nat.le_of_lt Nat.lt_two_pow_self)
    _ = _ := by rw [div_pow,div_pow];ring

lemma normalized_laplace_polynomial_tail_bound (c : ℕ → E) (M r s ξ : ℝ)
    (hM : 0 ≤ M) (hr : 0 < r) (hs : 0 < s) (hs1 : s ≤ 1) (hξ : 0 < ξ)
    (hc : ∀ j : ℕ, ‖c j‖ ≤ M/r^j) (L : ℕ) :
    ξ^s*‖∫ t in Ioi r,(Real.exp (-(ξ*t))*t^(s-1)) •
      (∑ j ∈ Finset.range L,t^j • c j)‖ ≤
      M*(2/r)^L*Real.Gamma s*(L.factorial:ℝ)/ξ^L := by
  apply normalized_laplace_remainder_factorial_bound _ _ measurableSet_Ioi
    (Ioi_subset_Ioi hr.le) s ξ (M*(2/r)^L) L hs hs1 hξ (by positivity)
  · have hm (j : ℕ) : AEStronglyMeasurable (fun t:ℝ => t^j • c j)
          (volume.restrict (Ioi r)) :=
        (by fun_prop : Measurable (fun t:ℝ => t^j)).aestronglyMeasurable.smul
          aestronglyMeasurable_const
    convert Finset.aestronglyMeasurable_sum (Finset.range L) (fun j _ => hm j) using 1
    ext t
    simp only [Finset.sum_apply]
  · intro t ht
    exact finite_polynomial_tail_pointwise_bound c M r t hM hr ht.le hc L

lemma exp_neg_factorial_bound (ε x : ℝ) (hε : 0 < ε) (hx : 0 < x) (L : ℕ) :
    Real.exp (-(ε*x)) ≤ (ε⁻¹)^L*(L.factorial:ℝ)/x^L := by
  have he := (div_le_iff₀ (by positivity : (0:ℝ) < (L.factorial:ℝ))).mp
    (Real.pow_div_factorial_le_exp (ε*x) (by positivity) L)
  have hp : Real.exp (-(ε*x))*(ε*x)^L ≤ (L.factorial:ℝ) := by
    calc
      _ ≤ Real.exp (-(ε*x))*((L.factorial:ℝ)*Real.exp (ε*x)) :=
        mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using he) (by positivity)
      _ = _ := by rw [Real.exp_neg];field_simp
  apply (le_div_iff₀ (pow_pos hx _)).2
  have ht := mul_le_mul_of_nonneg_right hp (le_of_lt (pow_pos (inv_pos.mpr hε) L))
  rw [mul_pow] at ht
  calc
    _ = (Real.exp (-(ε*x))*(ε^L*x^L))*(ε⁻¹)^L := by
      rw [inv_pow]
      field_simp
    _ ≤ (L.factorial:ℝ)*(ε⁻¹)^L := ht
    _ = _ := by ring

lemma normalized_outer_exp_factorial_bound (s ε x : ℝ) (hs1 : s ≤ 1)
    (hε : 0 < ε) (hx : 1 ≤ x) (L : ℕ) :
    x^s*Real.exp (-(ε*x)) ≤ (2/ε)*(2/ε)^L*(L.factorial:ℝ)/x^L := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hη : 0 < ε/2 := half_pos hε
  have hb1 := exp_neg_factorial_bound (ε/2) x hη hx0 1
  have hbL := exp_neg_factorial_bound (ε/2) x hη hx0 L
  have hxpow : x^s ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hs1
  have hxexp : x*Real.exp (-((ε/2)*x)) ≤ 2/ε := by
    have ht := mul_le_mul_of_nonneg_left hb1 hx0.le
    simpa only [pow_one,Nat.factorial_one,Nat.cast_one,mul_one,inv_div,one_div,
      mul_div_cancel₀ _ hx0.ne'] using ht
  calc
    _ ≤ x*Real.exp (-(ε*x)) := mul_le_mul_of_nonneg_right hxpow (by positivity)
    _ = (x*Real.exp (-((ε/2)*x)))*Real.exp (-((ε/2)*x)) := by
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ (2/ε)*((ε/2)⁻¹^L*(L.factorial:ℝ)/x^L) :=
      mul_le_mul hxexp hbL (by positivity) (by positivity)
    _ = _ := by rw [inv_div];field_simp

end WP.Analysis
