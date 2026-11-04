import Mathlib

/-! Scalar bounds for a second-order prefactor times a genuine profile and for the child complexity shift. -/

noncomputable section
open Set

noncomputable section
namespace WP.Analysis
lemma child_first_order_parent_scale (c δ h L C B : ℝ)
    (hh : 2 ≤ h) (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hδ : |δ| ≤ B*L^2)
    (he : |c-(1-δ/(h-1))| ≤ C*L^4/(h-1)^2) :
    |c-(1-δ/h)| ≤ (4*C+2*B)*L^4/h^2 := by
  have hp : 0<h := by linarith
  have hm : 0<h-1 := by linarith
  have hsq : h^2 ≤ 4*(h-1)^2 := by nlinarith
  have hcscale : C*L^4/(h-1)^2 ≤ 4*C*L^4/h^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hm) (sq_pos_of_pos hp)).2
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ C*L^4 by positivity)]
  have hdscale : |δ/(h-1)-δ/h| ≤ 2*B*L^4/h^2 := by
    have h0 : δ/(h-1)-δ/h=δ/(h*(h-1)) := by field_simp <;> ring
    rw [h0,abs_div,abs_of_pos (mul_pos hp hm)]
    calc
      _ ≤ B*L^2/(h*(h-1)) := div_le_div_of_nonneg_right hδ (by positivity)
      _ ≤ 2*B*L^2/h^2 := by
        apply (div_le_div_iff₀ (mul_pos hp hm) (sq_pos_of_pos hp)).2
        have hs : h^2 ≤ 2*(h*(h-1)) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ B*L^2 by positivity)]
      _ ≤ 2*B*L^4/h^2 := by
        have h24 : L^2 ≤ L^4 := pow_le_pow_right₀ hL (by norm_num)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h24 (by positivity)) (sq_nonneg h)
  have htriangle := abs_sub (c-(1-δ/(h-1))) (δ/(h-1)-δ/h)
  have heq : (c-(1-δ/(h-1)))-(δ/(h-1)-δ/h)=c-(1-δ/h) := by ring
  rw [heq] at htriangle
  exact htriangle.trans ((add_le_add (he.trans hcscale) hdscale).trans (by ring_nf;exact le_rfl))
end WP.Analysis

noncomputable section
open Set
namespace WP.Analysis
lemma second_prefactor_child_error (a b δ r c t L M N C Q : ℝ)
    (ht : t∈Icc 0 1) (hL : 1 ≤ L) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hδ : |δ| ≤ N*L^2) (hc : 0 ≤ c ∧ c ≤ 1)
    (hr : |r-(a*t+b*t^2)| ≤ C*t^3)
    (hp : |c-(1-δ*t)| ≤ Q*L^4*t^2) :
    |r*c-(a*t+(b-a*δ)*t^2)| ≤ (C+2*M*Q+M*N)*L^4*t^3 := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have ht2 : t^2 ≤ t := by nlinarith [ht.1,ht.2]
  have hcen : |a*t+b*t^2| ≤ 2*M*t := by
    calc
      _ ≤ |a*t|+|b*t^2| := abs_add_le _ _
      _ = |a| *t+|b| *t^2 := by rw [abs_mul,abs_of_nonneg ht.1,abs_mul,abs_of_nonneg (sq_nonneg t)]
      _ ≤ M*t+M*t^2 := add_le_add (mul_le_mul_of_nonneg_right ha ht.1)
        (mul_le_mul_of_nonneg_right hb (sq_nonneg t))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht2 hM]
  have hfirst : |(r-(a*t+b*t^2))*c| ≤ C*t^3 := by
    rw [abs_mul,abs_of_nonneg hc.1]
    simpa only [mul_one] using mul_le_mul hr hc.2 hc.1 (show 0 ≤ C*t^3 by positivity)
  have hsecond : |(a*t+b*t^2)*(c-(1-δ*t))| ≤ 2*M*Q*L^4*t^3 := by
    rw [abs_mul]
    calc
      _ ≤ (2*M*t)*(Q*L^4*t^2) := mul_le_mul hcen hp (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hthird : |b*δ*t^3| ≤ M*N*L^4*t^3 := by
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg ht.1 _)]
    have hL24 : L^2 ≤ L^4 := pow_le_pow_right₀ hL (by norm_num)
    calc
      _ ≤ (M*(N*L^2))*t^3 := mul_le_mul_of_nonneg_right
        (mul_le_mul hb hδ (abs_nonneg _) hM) (by positivity)
      _ ≤ (M*(N*L^4))*t^3 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL24 hN) hM) (by positivity)
      _ = _ := by ring
  have he : r*c-(a*t+(b-a*δ)*t^2)=
      (r-(a*t+b*t^2))*c+(a*t+b*t^2)*(c-(1-δ*t))-b*δ*t^3 := by ring
  rw [he]
  calc
    _ ≤ |(r-(a*t+b*t^2))*c|+|(a*t+b*t^2)*(c-(1-δ*t))|+|b*δ*t^3| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C*t^3+2*M*Q*L^4*t^3+M*N*L^4*t^3 :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ ≤ _ := by
      have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
      have hm := mul_le_mul_of_nonneg_right hL4 (show 0 ≤ C*t^3 by positivity)
      nlinarith
end WP.Analysis

namespace WP.Analysis
lemma second_prefactor_child_error_div (a b δ r c h L M N C Q : ℝ)
    (hh : 1 ≤ h) (hL : 1 ≤ L) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hδ : |δ| ≤ N*L^2) (hc : 0 ≤ c ∧ c ≤ 1)
    (hr : |r-(a/h+b/h^2)| ≤ C/h^3)
    (hp : |c-(1-δ/h)| ≤ Q*L^4/h^2) :
    |r*c-a/h-(b-a*δ)/h^2| ≤ (C+2*M*Q+M*N)*L^4/h^3 := by
  have hhp : 0<h := lt_of_lt_of_le zero_lt_one hh
  have ht : (1/h)∈Icc (0:ℝ) 1 := ⟨by positivity,(div_le_one hhp).2 hh⟩
  have hr' : |r-(a*(1/h)+b*(1/h)^2)| ≤ C*(1/h)^3 := by
    convert hr using 1 <;> ring
  have hp' : |c-(1-δ*(1/h))| ≤ Q*L^4*(1/h)^2 := by
    convert hp using 1 <;> ring
  have he := second_prefactor_child_error a b δ r c (1/h) L M N C Q ht hL hM hN hC hQ ha hb hδ hc hr' hp'
  convert he using 1 <;> ring
end WP.Analysis

noncomputable section
namespace WP.Analysis
lemma finite_weighted_two_scales_error {ι : Type*} (s : Finset ι)
    (coeff f u v : ι→ℝ) (a b E : ℝ)
    (hc : ∀ i∈s,0 ≤ coeff i) (he : ∀ i∈s,|f i-a*u i-b*v i| ≤ E) :
    |(∑ i∈s,coeff i*f i)-a*(∑ i∈s,coeff i*u i)-b*(∑ i∈s,coeff i*v i)| ≤
      E*(∑ i∈s,coeff i) := by
  have heq : (∑ i∈s,coeff i*f i)-a*(∑ i∈s,coeff i*u i)-b*(∑ i∈s,coeff i*v i)=
      ∑ i∈s,coeff i*(f i-a*u i-b*v i) := by
    simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    _ ≤ ∑ i∈s,|coeff i*(f i-a*u i-b*v i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i∈s,coeff i*E := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (hc i hi)]
      exact mul_le_mul_of_nonneg_left (he i hi) (hc i hi)
    _ = _ := by rw [←Finset.sum_mul];ring
end WP.Analysis

namespace WP.Analysis
lemma second_zero_ratio_profile_error (r c a h L C Q : ℝ)
    (hh : 0<h) (hL : 1 ≤ L) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hc : 0 ≤ c ∧ c ≤ 1)
    (hr : |r-a/h^2| ≤ C/h^3) (hp : |1-c| ≤ Q*L^2/h) :
    |r*c-a/h^2| ≤ (C+|a| *Q)*L^2/h^3 := by
  have he : r*c-a/h^2=(r-a/h^2)*c+(a/h^2)*(c-1) := by ring
  rw [he]
  calc
    _ ≤ |(r-a/h^2)*c|+|(a/h^2)*(c-1)| := abs_add_le _ _
    _ = |r-a/h^2| *c+(|a|/h^2)*|1-c| := by
      rw [abs_mul,abs_of_nonneg hc.1,abs_mul,abs_div,abs_pow,abs_of_pos hh,abs_sub_comm c 1]
    _ ≤ (C/h^3)*1+(|a|/h^2)*(Q*L^2/h) :=
      add_le_add (mul_le_mul hr hc.2 hc.1 (by positivity))
        (mul_le_mul_of_nonneg_left hp (by positivity))
    _ ≤ (C/h^3)*L^2+(|a|/h^2)*(Q*L^2/h) := by
      apply add_le_add ?_ le_rfl
      have hL2 : 1 ≤ L^2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ = _ := by field_simp
end WP.Analysis
