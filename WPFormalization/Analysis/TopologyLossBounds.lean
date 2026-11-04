import WPFormalization.Analysis.UniformLossTail

/-! Uniform subset counts, filtered loss-power tails, and monotonicity of the loss scale. -/
noncomputable section
namespace WP.Analysis
open Finset Finset.Nat
lemma subset_loss_choose_sum (p r : ℕ) :
    (∑ s ∈ range (r+1), Nat.choose p s) ≤ Nat.choose (p+r) r := by
  rw [Nat.add_choose_eq,sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_le_sum
  intro s hs
  have hs0 := mem_range.mp hs
  have he : 1 ≤ Nat.choose r (r-s) := Nat.choose_pos (by omega)
  nlinarith only [he]
lemma subset_loss_factorial_sum (p r : ℕ) :
    ((r.factorial:ℝ)*(∑ s ∈ range (r+1), (Nat.choose p s:ℝ))) ≤ ((p+r:ℕ):ℝ)^r := by
  have hs : (∑ s ∈ range (r+1), (Nat.choose p s:ℝ)) ≤ (Nat.choose (p+r) r:ℝ) := by
    exact_mod_cast subset_loss_choose_sum p r
  calc
    _ ≤ (r.factorial:ℝ)*(Nat.choose (p+r) r:ℝ) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((p+r).descFactorial r:ℝ) := by rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
    _ ≤ _ := by exact_mod_cast Nat.descFactorial_le_pow (p+r) r
lemma finite_loss_power_tail_filter (p B h : ℝ) (L R : ℕ) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hh : 0 < h) (hL : 1 ≤ L)
    (hcut : 2*Real.exp 1*B*(p+(R:ℝ)+2) ≤ h) :
    (∑ r ∈ Finset.range (R+1), if L ≤ r then (B*(p+r)/h)^r else 0) ≤
      2*(B*(p+L)/h)^L := by
  by_cases hLR : L ≤ R+1
  · have hsplit : R+1=L+(R+1-L) := by omega
    rw [hsplit,Finset.sum_range_add]
    have hz : (∑ r ∈ Finset.range L, if L ≤ r then (B*(p+r)/h)^r else 0)=0 := by
      apply Finset.sum_eq_zero
      intro r hr
      exact if_neg (by have he:=Finset.mem_range.mp hr;omega)
    rw [hz,zero_add]
    simp only [Nat.le_add_right,ite_true]
    apply finite_loss_power_tail p B h L (R+1-L) hp hB hh hL
    convert hcut using 1
    have he : L+(R+1-L)=R+1 := by omega
    rw [he,Nat.cast_add,Nat.cast_one]
    ring
  · have hz : (∑ r ∈ Finset.range (R+1), if L ≤ r then (B*(p+r)/h)^r else 0)=0 := by
      apply Finset.sum_eq_zero
      intro r hr
      exact if_neg (by have he:=Finset.mem_range.mp hr;omega)
    rw [hz]
    positivity
lemma loss_scale_bound_mono (C C' B B' x h : ℝ) (L : ℕ)
    (hC : 0 ≤ C) (hCC : C ≤ C') (hB : 0 ≤ B) (hBB : B ≤ B')
    (hx : 0 ≤ x) (hh : 0 ≤ h) : C*(B*x/h)^L ≤ C'*(B'*x/h)^L := by
  apply mul_le_mul hCC
  · apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBB hx) hh
  · positivity
  · linarith
end WP.Analysis
