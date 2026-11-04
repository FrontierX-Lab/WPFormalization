import WPFormalization.HigherOrder.TriangularLocality
import Mathlib.RingTheory.PowerSeries.Binomial

/-! Exact inverse-linear shift coefficients and the normalized product estimate of Appendix C.5(c). Finite products with total exponent a and shift degree q satisfy the bound S^(2q)/q! when a+q <= j and all shifts have magnitude at most j <= S. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma inverse_linear_pow_eq_rescale (c : ℝ) (a : ℕ) :
    ((1-C c*PowerSeries.X : Series)⁻¹)^a=
      PowerSeries.rescale c ((PowerSeries.invOneSubPow ℝ a).val) := by
  rw [PowerSeries.inv_pow]
  symm
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr
  have he:=(PowerSeries.invOneSubPow ℝ a).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at he
  have ht:=congrArg (PowerSeries.rescale c) he
  simpa only [map_mul,map_pow,map_sub,map_one,PowerSeries.rescale_X] using ht

lemma inverse_linear_pow_coeff (c : ℝ) (a q : ℕ) (ha : 1≤a) :
    PowerSeries.coeff q (((1-C c*PowerSeries.X : Series)⁻¹)^a)=
      (Nat.choose (a+q-1) q:ℝ)*c^q := by
  rw [inverse_linear_pow_eq_rescale,PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℝ a (by omega),PowerSeries.coeff_mk]
  have he : a-1+q=a+q-1 := by omega
  rw [he]
  have hc : Nat.choose (a+q-1) (a-1)=Nat.choose (a+q-1) q := by
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hc]
  ring

lemma inverse_linear_pow_coeff_bound (c c₀ : ℝ) (a q : ℕ) (ha : 1≤a) (hc : |c|≤c₀) :
    |PowerSeries.coeff q (((1-C c*PowerSeries.X : Series)⁻¹)^a)|≤
      (((a+q:ℕ):ℝ)*c₀)^q/(q.factorial:ℝ) := by
  rw [inverse_linear_pow_coeff c a q ha,abs_mul,abs_pow,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hchoose : (Nat.choose (a+q-1) q:ℝ)≤(((a+q:ℕ):ℝ)^q)/(q.factorial:ℝ) := by
    calc _≤((a+q-1:ℕ):ℝ)^q/(q.factorial:ℝ):=Nat.choose_le_pow_div q (a+q-1)
         _≤_:=(div_le_div_of_nonneg_right
           (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show a+q-1≤a+q by omega)) q) (by positivity))
  have hc₀ : 0≤c₀:=(abs_nonneg c).trans hc
  have hp:=pow_le_pow_left₀ (abs_nonneg c) hc q
  calc _≤((((a+q:ℕ):ℝ)^q)/(q.factorial:ℝ))*c₀^q:=
         mul_le_mul hchoose hp (pow_nonneg (abs_nonneg c) q) (by positivity)
       _=_:=by rw [mul_pow];ring

lemma inverse_linear_pow_coeff_normalized (c S : ℝ) (a q j : ℕ)
    (ha : 1≤a) (haj : a+q≤j) (hc : |c|≤j) (hS : (j:ℝ)≤S) :
    |PowerSeries.coeff q (((1-C c*PowerSeries.X : Series)⁻¹)^a)|≤
      S^(2*q)/(q.factorial:ℝ) := by
  have hjS : 0≤S:=le_trans (Nat.cast_nonneg j) hS
  apply (inverse_linear_pow_coeff_bound c (j:ℝ) a q ha hc).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have haS : ((a+q:ℕ):ℝ)≤S:=(show ((a+q:ℕ):ℝ)≤(j:ℝ) by exact_mod_cast haj).trans hS
  have hprod : ((a+q:ℕ):ℝ)*(j:ℝ)≤S^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr haS) (Nat.cast_nonneg j : (0:ℝ)≤j)]
  calc _≤(S^2)^q:=pow_le_pow_left₀ (by positivity) hprod q
       _=_:=by rw [pow_mul]
lemma inverse_linear_pow_abs_coeff_le (c c₀ : ℝ) (a q : ℕ) (hc : |c|≤c₀) :
    |PowerSeries.coeff q (((1-C c*PowerSeries.X : Series)⁻¹)^a)|≤
      PowerSeries.coeff q (((1-C c₀*PowerSeries.X : Series)⁻¹)^a) := by
  by_cases ha : a=0
  · subst a
    simp only [pow_zero,PowerSeries.coeff_one]
    split_ifs <;>norm_num
  · rw [inverse_linear_pow_coeff c a q (by omega),inverse_linear_pow_coeff c₀ a q (by omega),
      abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg c) hc q) (Nat.cast_nonneg _)

lemma abs_coeff_mul_le {f₁ f₂ g₁ g₂ : Series}
    (h₁ : ∀n:ℕ,|PowerSeries.coeff n f₁|≤PowerSeries.coeff n g₁)
    (h₂ : ∀n:ℕ,|PowerSeries.coeff n f₂|≤PowerSeries.coeff n g₂) (q:ℕ) :
    |PowerSeries.coeff q (f₁*f₂)|≤PowerSeries.coeff q (g₁*g₂) := by
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  rw [abs_mul]
  exact mul_le_mul (h₁ ij.1) (h₂ ij.2) (abs_nonneg _) ((abs_nonneg _).trans (h₁ ij.1))

lemma abs_coeff_prod_le {ι:Type*} (s:Finset ι) (f g:ι→Series)
    (h:∀i∈s,∀n:ℕ,|PowerSeries.coeff n (f i)|≤PowerSeries.coeff n (g i)) (q:ℕ) :
    |PowerSeries.coeff q (∏i∈s,f i)|≤PowerSeries.coeff q (∏i∈s,g i) := by
  classical
  induction s using Finset.induction_on generalizing q with
  | empty =>
    simp only [Finset.prod_empty,PowerSeries.coeff_one]
    split_ifs <;>norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    apply abs_coeff_mul_le
    · exact h i (Finset.mem_insert_self _ _)
    · intro n
      exact ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)) n

lemma inverse_linear_product_coeff_bound {ι:Type*} (s:Finset ι) (a:ι→ℕ) (c:ι→ℝ)
    (c₀ : ℝ) (hc : ∀i∈s,|c i|≤c₀) (q:ℕ) :
    |PowerSeries.coeff q (∏i∈s,((1-C (c i)*PowerSeries.X : Series)⁻¹)^(a i))|≤
      PowerSeries.coeff q (((1-C c₀*PowerSeries.X : Series)⁻¹)^(∑i∈s,a i)) := by
  rw [←Finset.prod_pow_eq_pow_sum]
  apply abs_coeff_prod_le
  intro i hi n
  exact inverse_linear_pow_abs_coeff_le (c i) c₀ (a i) n (hc i hi)

lemma inverse_linear_product_coeff_normalized {ι:Type*} (s:Finset ι) (a:ι→ℕ) (c:ι→ℝ)
    (S : ℝ) (q j:ℕ) (ha : 1≤∑i∈s,a i) (haj : (∑i∈s,a i)+q≤j)
    (hc : ∀i∈s,|c i|≤j) (hS : (j:ℝ)≤S) :
    |PowerSeries.coeff q (∏i∈s,((1-C (c i)*PowerSeries.X : Series)⁻¹)^(a i))|≤S^(2*q)/(q.factorial:ℝ) := by
  have hj:=inverse_linear_product_coeff_bound s a c (j:ℝ) hc q
  have hnon : 0≤PowerSeries.coeff q (((1-C (j:ℝ)*PowerSeries.X : Series)⁻¹)^(∑i∈s,a i)) := by
    rw [inverse_linear_pow_coeff _ _ _ ha]
    positivity
  rw [←abs_of_nonneg hnon] at hj
  exact hj.trans (inverse_linear_pow_coeff_normalized (j:ℝ) S _ q j ha haj
    (by rw [abs_of_nonneg (Nat.cast_nonneg j)]) hS)
end WP.HigherOrder
