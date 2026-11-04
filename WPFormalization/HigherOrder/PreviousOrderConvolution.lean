import Mathlib
/-! Reindexing strict previous-order convolutions into the single common
positive loss convolution used by the four-stage actual remainder induction.
These finite numerical inequalities use no hierarchy or asymptotic input. -/
noncomputable section
namespace WP.HigherOrder
lemma previous_order_convolution_le_Icc (A B:ℝ) (hA:0 ≤ A) (hB:1 ≤ B) (hAB:A ≤ B)
    (L:ℕ) (hL:1 ≤ L) (e:ℕ→ℝ) (he:∀j,0 ≤ e j) :
    (∑i∈Finset.range (L-1),A^i*e (L-1-i)) ≤ ∑j∈Finset.Icc 1 L,B^j*e (L-j):=by
  classical
  apply Finset.sum_le_sum_of_injOn (fun i:ℕ=>i+1)
  · intro i hi j hj hij
    change i+1=j+1 at hij
    omega
  · intro j hj
    obtain ⟨i,hi,hij⟩:=Finset.mem_image.mp hj
    have hiL:=Finset.mem_range.mp hi
    subst j
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i hi
    have hpow:A^i ≤ B^(i+1):=(pow_le_pow_left₀ hA hAB i).trans (pow_le_pow_right₀ hB (by omega))
    have hj:L-1-i=L-(i+1):=by omega
    rw[hj]
    exact mul_le_mul_of_nonneg_right hpow (he _)
  · intro j hj hnot
    exact mul_nonneg (pow_nonneg (show 0 ≤ B by linarith) j) (he _)

lemma previous_order_top_le_Icc (B:ℝ) (hB:1 ≤ B) (L:ℕ) (hL:1 ≤ L)
    (e:ℕ→ℝ) (he:∀j,0 ≤ e j) :
    e (L-1) ≤ ∑j∈Finset.Icc 1 L,B^j*e (L-j):=by
  have hp:e (L-1) ≤ B^1*e (L-1):=by rw[pow_one];nlinarith[he (L-1)]
  exact hp.trans (Finset.single_le_sum (f:=fun j:ℕ=>B^j*e (L-j)) (fun j hj=>mul_nonneg (pow_nonneg (show 0 ≤ B by linarith) j) (he _))
    (Finset.mem_Icc.mpr ⟨le_rfl,hL⟩))

lemma previous_order_linear_convolutions_bound (A B:ℝ) (hA:0 ≤ A) (hB:1 ≤ B) (hAB:A ≤ B)
    (L:ℕ) (hL:1 ≤ L) (e:ℕ→ℝ) (he:∀j,0 ≤ e j) :
    e (L-1)+(∑i∈Finset.range (L-1),A^i*e (L-1-i))+
      (∑i∈Finset.range (L-1),A^i*e (L-1-i))+A^L ≤
      3*(∑j∈Finset.Icc 1 L,B^j*e (L-j))+B^L:=by
  have hconv:=previous_order_convolution_le_Icc A B hA hB hAB L hL e he
  have htop:=previous_order_top_le_Icc B hB L hL e he
  have hpow:=pow_le_pow_left₀ hA hAB L
  linarith
end WP.HigherOrder
