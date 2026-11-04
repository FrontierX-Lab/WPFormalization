import Mathlib

/-! Finite weighted error bounds used to compare genuine child profiles with their zero-degree leading term. These scalar lemmas use only standard axioms. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP.Analysis
lemma finite_weighted_profile_error {ι : Type*} (s : Finset ι)
    (c f b : ι → ℝ) (R E : ℝ) (hR : 0 ≤ R)
    (hc : ∀ i ∈ s, 0 ≤ c i) (herr : ∀ i ∈ s, |f i-b i| ≤ E) :
    |R*(∑ i ∈ s, c i*f i)-R*(∑ i ∈ s, c i*b i)| ≤ R*E*(∑ i ∈ s, c i) := by
  have heq : R*(∑ i ∈ s, c i*f i)-R*(∑ i ∈ s, c i*b i)=
      R*(∑ i ∈ s, c i*(f i-b i)) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [heq,abs_mul,abs_of_nonneg hR]
  calc _ ≤ R*(∑ i ∈ s, |c i*(f i-b i)|) := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hR
       _ ≤ R*(∑ i ∈ s, c i*E) := by
         apply mul_le_mul_of_nonneg_left _ hR
         apply Finset.sum_le_sum
         intro i hi
         rw [abs_mul,abs_of_nonneg (hc i hi)]
         exact mul_le_mul_of_nonneg_left (herr i hi) (hc i hi)
       _ = _ := by rw [←Finset.sum_mul];ring
end WP.Analysis
namespace WP.Analysis
lemma layer_first_order_error_bound (A h B K R Q E S r₁ r₂ a b c n s : ℝ)
    (hh : 0<h) (hB : 1 ≤ B) (hK : 0 ≤ K) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hr₁b : r₁ ≤ R/h) (hr₂b : r₂ ≤ R/h)
    (hr₁e : |r₁-A/h| ≤ E/h^2) (hr₂e : |r₂-A/h| ≤ E/h^2)
    (hb : b ∈ Set.Icc 0 (K*B)) (hn : n ∈ Set.Icc 0 B)
    (hae : |a-b| ≤ Q*B^2/h*(K*B)) (hce : |c-n| ≤ Q*B^2/h*B)
    (hs : s ∈ Set.Icc 0 (S*B/h^2)) :
    |r₁*a+2*r₂*c+s-(A/h)*(b+2*n)| ≤
      (R*Q*(K+2)+E*(K+2)+S)*B^3/h^2 := by
  have hBp : 0 ≤ B := by linarith
  have hB3 : B ≤ B^3 := by nlinarith [mul_nonneg hBp (show 0≤B^2-1 by nlinarith)]
  have heq : r₁*a+2*r₂*c+s-(A/h)*(b+2*n)=
      (((r₁*(a-b)+2*r₂*(c-n))+(r₁-A/h)*b)+2*(r₂-A/h)*n)+s := by ring
  rw [heq]
  have habs : |(((r₁*(a-b)+2*r₂*(c-n))+(r₁-A/h)*b)+2*(r₂-A/h)*n)+s| ≤
      r₁*|a-b|+2*r₂*|c-n|+|r₁-A/h| *b+2*|r₂-A/h| *n+s := by
    have h1 := abs_add_le ((((r₁*(a-b)+2*r₂*(c-n))+(r₁-A/h)*b)+2*(r₂-A/h)*n)) s
    have h2 := abs_add_le (((r₁*(a-b)+2*r₂*(c-n))+(r₁-A/h)*b)) (2*(r₂-A/h)*n)
    have h3 := abs_add_le ((r₁*(a-b)+2*r₂*(c-n))) ((r₁-A/h)*b)
    have h4 := abs_add_le (r₁*(a-b)) (2*r₂*(c-n))
    simp only [abs_mul,abs_of_nonneg hr₁,abs_of_nonneg hr₂,abs_of_nonneg hb.1,
      abs_of_nonneg hn.1,abs_of_nonneg hs.1,abs_of_nonneg (show (0:ℝ)≤2 by norm_num)] at *
    linarith
  calc _ ≤ r₁*|a-b|+2*r₂*|c-n|+|r₁-A/h| *b+2*|r₂-A/h| *n+s := habs
       _ ≤ (R/h)*(Q*B^2/h*(K*B))+2*(R/h)*(Q*B^2/h*B)+
           (E/h^2)*(K*B)+2*(E/h^2)*B+S*B/h^2 := by
         apply add_le_add _ hs.2
         apply add_le_add
         · apply add_le_add
           · exact add_le_add (mul_le_mul hr₁b hae (abs_nonneg _) (by positivity))
               (mul_le_mul (mul_le_mul_of_nonneg_left hr₂b (by norm_num)) hce (abs_nonneg _) (by positivity))
           · exact mul_le_mul hr₁e hb.2 hb.1 (by positivity)
         · exact mul_le_mul (mul_le_mul_of_nonneg_left hr₂e (by norm_num)) hn.2 hn.1 (by positivity)
       _ = (R*Q*(K+2)*B^3+E*(K+2)*B+S*B)/h^2 := by ring
       _ ≤ _ := by
         apply div_le_div_of_nonneg_right _ (sq_nonneg h)
         have h1 := mul_le_mul_of_nonneg_left hB3 (show 0≤E*(K+2) by positivity)
         have h2 := mul_le_mul_of_nonneg_left hB3 hS
         nlinarith
end WP.Analysis
