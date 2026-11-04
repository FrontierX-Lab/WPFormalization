import WPFormalization.Intersection.Finite
import WPFormalization.Intersection.PrimitiveMajorant
/-! Classical normalized dilaton and the complete positive genus-one case of
Appendix B. No estimate for higher genus is assumed or asserted here. -/
noncomputable section
namespace WP
lemma pureC_dilaton (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) : pureC P g (1 :: d) = pureC P g d := by
  have hc : complexity g (d.length+1) = complexity g d.length+1 := by
    unfold complexity
    unfold Stable at hs
    omega
  have hh : 0 < (complexity g d.length : ℝ) := by
    have hn : 0 < complexity g d.length := by
      unfold complexity
      unfold Stable at hs
      omega
    exact_mod_cast hn
  have hr : 2*(g : ℝ)-2+d.length = (complexity g d.length : ℝ) := by
    unfold complexity
    rw [Nat.cast_sub (by unfold Stable at hs; omega)]
    push_cast
    ring
  have hdil := P.dilaton g (d.map Int.ofNat) (by simpa using hs)
  simp only [List.length_map] at hdil
  unfold pureC pure
  simp only [List.length_cons, List.map_cons, List.prod_cons]
  change P.psi g (Int.ofNat 1 :: d.map Int.ofNat) =
    (2*(g : ℝ)-2+d.length)*P.psi g (d.map Int.ofNat) at hdil
  rw [show oddFactorial 1 = 3 from by decide, hdil, hr, hc]
  simp only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  rw [Real.Gamma_add_one hh.ne', pow_succ]
  have hG : Real.Gamma (complexity g d.length : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hh).ne'
  field_simp [hh.ne', hG]
  <;> ring
end WP
namespace WP
lemma length_le_sum_of_positive (d : List ℕ) (hd : ∀ k ∈ d, 0 < k) :
    d.length ≤ d.sum := by
  induction d with
  | nil => simp
  | cons k d ih =>
    have hk := hd k (by simp)
    have hh := ih (fun j hj => hd j (by simp [hj]))
    simp only [List.length_cons, List.sum_cons]
    omega
lemma eq_replicate_one_of_positive_sum (d : List ℕ) (hd : ∀ k ∈ d, 0 < k)
    (hs : d.sum = d.length) : d = List.replicate d.length 1 := by
  induction d with
  | nil => rfl
  | cons k d ih =>
    have hk := hd k (by simp)
    have hd' : ∀ j ∈ d, 0 < j := fun j hj => hd j (by simp [hj])
    have hl := length_le_sum_of_positive d hd'
    simp only [List.length_cons, List.sum_cons] at hs
    have hkeq : k = 1 := by omega
    have hsum : d.sum = d.length := by omega
    rw [List.length_cons, List.replicate_succ, hkeq, ih hd' hsum]
    simp
lemma pureC_genus_one_ones (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) :
    pureC P 1 (List.replicate n 1) = 1/6 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      norm_num [pureC, pure, complexity, oddFactorial, Finset.prod_range_succ, P.base₁]
    | succ n =>
      rw [List.replicate_succ, pureC_dilaton P 1 _ (by simp [Stable])]
      exact ih (by omega)
lemma pureC_genus_one (P : PsiTheory) (d : List ℕ) (hn : 1 ≤ d.length)
    (hd : ∀ k ∈ d, 0 < k) (hdim : d.sum = dimension 1 d.length) :
    pureC P 1 d = 1/6 := by
  have hs : d.sum = d.length := by simpa [dimension] using hdim
  rw [eq_replicate_one_of_positive_sum d hd hs]
  exact pureC_genus_one_ones P d.length hn
end WP

namespace WP
lemma primitive_bounds_genus_one (P : PsiTheory) (d : List ℕ)
    (hn : 1 ≤ d.length) (hd : ∀ k ∈ d, 0 < k)
    (hdim : d.sum = dimension 1 d.length) :
    1/6 ≤ pureC P 1 d ∧ pureC P 1 d ≤ 1 := by
  rw [pureC_genus_one P d hn hd hdim]
  norm_num
end WP
