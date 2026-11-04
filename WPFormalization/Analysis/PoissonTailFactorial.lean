import Mathlib
noncomputable section
namespace WP.Analysis
lemma descFactorial_half_order_le (N m j : ℕ) (hNm : m ≤ 2*N) (hNj : N ≤ j) :
    m.descFactorial j ≤ 4^N*N.factorial*N^(j-N) := by
  have hlow : m.descFactorial N ≤ 4^N*N.factorial := by
    calc _ ≤ (2*N).descFactorial N := Nat.descFactorial_le N hNm
         _ = N.factorial*(2*N).choose N := Nat.descFactorial_eq_factorial_mul_choose _ _
         _ ≤ N.factorial*2^(2*N) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
         _ = _ := by rw [pow_mul];ring
  have hhigh : (m-N).descFactorial (j-N) ≤ N^(j-N) :=
    (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  rw [←Nat.descFactorial_mul_descFactorial hNj]
  calc _ ≤ N^(j-N)*(4^N*N.factorial) := Nat.mul_le_mul hhigh hlow
       _ = _ := by ring

lemma factorial_ratio_inverse_order_le (h : ℝ) (hh : 0 < h) (N m a : ℕ)
    (ha : a ≤ m) (hm : m ≤ 2*N) (hj : N ≤ m-a) (hN : (N:ℝ) ≤ h) :
    (m.factorial:ℝ)/(a.factorial:ℝ)/h^(m-a) ≤ 4^N*(N.factorial:ℝ)/h^N := by
  have hfactor : (m.factorial:ℝ)/(a.factorial:ℝ)=(m.descFactorial (m-a):ℝ) := by
    have ht := Nat.factorial_mul_descFactorial (show m-a ≤ m by omega)
    rw [show m-(m-a)=a by omega] at ht
    have ht' : (a.factorial:ℝ)*(m.descFactorial (m-a):ℝ)=(m.factorial:ℝ) := by exact_mod_cast ht
    apply (div_eq_iff (by positivity : (a.factorial:ℝ)≠0)).mpr
    nlinarith
  rw [hfactor]
  have hb : (m.descFactorial (m-a):ℝ) ≤ (4:ℝ)^N*(N.factorial:ℝ)*(N:ℝ)^(m-a-N) := by
    exact_mod_cast descFactorial_half_order_le N m (m-a) hm hj
  have hp : (N:ℝ)^(m-a-N) ≤ h^(m-a-N) := pow_le_pow_left₀ (Nat.cast_nonneg N) hN _
  calc _ ≤ ((4:ℝ)^N*(N.factorial:ℝ)*h^(m-a-N))/h^(m-a) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact hb.trans (mul_le_mul_of_nonneg_left hp (by positivity))
       _ = _ := by
          have hpow : h^(m-a)=h^N*h^(m-a-N) := by rw [←pow_add,show N+(m-a-N)=m-a by omega]
          rw [hpow]
          field_simp
end WP.Analysis
