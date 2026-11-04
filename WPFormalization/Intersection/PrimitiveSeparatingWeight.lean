import WPFormalization.Statements.IntersectionInterface
import Mathlib.Data.Nat.Choose.Sum
/-! The full finite combinatorial majorant for Appendix B separating weights.
A beta-binomial convolution eliminates the subset-size sum exactly. This file
proves the actual factorial/genus weight bound, without assuming any
intersection-number upper bound. The later support argument must still connect
these weights to the actual DVV factors. -/
noncomputable section
namespace WP
/-- Beta integral at positive integer arguments, written as its factorial ratio. -/
def factorialBeta (a b : ℕ) : ℝ := (a.factorial : ℝ)*b.factorial/(a+b+1).factorial
lemma factorialBeta_step (a b : ℕ) :
    factorialBeta (a+1) b+factorialBeta a (b+1) = factorialBeta a b := by
  unfold factorialBeta
  have ha : a+1+b+1 = (a+b+1)+1 := by omega
  have hb : a+(b+1)+1 = (a+b+1)+1 := by omega
  rw [ha,hb]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hf : ((a+b).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp [hf]
  <;> ring
lemma factorialBeta_convolution (a b N : ℕ) :
    (∑ m ∈ Finset.range (N+1), (N.choose m : ℝ)*factorialBeta (a+m) (b+(N-m))) =
      factorialBeta a b := by
  induction N with
  | zero => simp
  | succ N ih =>
    change (∑ m ∈ Finset.range (N+2), ((N+1).choose m : ℝ)*
      (fun i j => factorialBeta (a+i) (b+j)) m (N+1-m)) = _
    rw [Finset.sum_choose_succ_mul (fun i j => factorialBeta (a+i) (b+j)) N]
    have he₁ : (∑ m ∈ Finset.range (N+1), (N.choose m : ℝ)*
        factorialBeta (a+m) (b+(N+1-m))) =
        ∑ m ∈ Finset.range (N+1), (N.choose m : ℝ)*
          factorialBeta (a+m) ((b+(N-m))+1) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm' := Finset.mem_range.mp hm
      congr 2
      omega
    rw [he₁,← Finset.sum_add_distrib]
    have he₂ : (∑ m ∈ Finset.range (N+1),
        ((N.choose m : ℝ)*factorialBeta (a+m) (b+(N-m)+1) +
          (N.choose m : ℝ)*factorialBeta (a+(m+1)) (b+(N-m)))) =
        ∑ m ∈ Finset.range (N+1), (N.choose m : ℝ)*factorialBeta (a+m) (b+(N-m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [show a+(m+1) = a+m+1 by omega,← mul_add,
        add_comm (factorialBeta _ _) (factorialBeta _ _),factorialBeta_step]
    rw [he₂]
    exact ih
lemma choose_interior_lower (K k : ℕ) (hk : 0 < k) (hK : k < K) :
    K ≤ K.choose k := by
  induction K generalizing k with
  | zero => omega
  | succ K ih =>
    by_cases hk1 : k = 1
    · subst k; simp
    · by_cases hkK : k = K
      · subst k; simp
      · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        rw [Nat.choose_succ_succ]
        have h₁ := ih j (by omega) (by omega)
        have h₂ : 1 ≤ K.choose (j+1) := Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
        simp only [Nat.succ_eq_add_one] at *
        omega
lemma factorialBeta_choose (a b : ℕ) :
    factorialBeta a b = 1/((a+b+1 : ℕ)*(Nat.choose (a+b) a : ℝ)) := by
  have he := Nat.choose_mul_factorial_mul_factorial (show a ≤ a+b by omega)
  have heR : (Nat.choose (a+b) a : ℝ)*a.factorial*b.factorial = (a+b).factorial := by
    have hh : a+b-a = b := by omega
    rw [hh] at he
    exact_mod_cast he
  unfold factorialBeta
  rw [Nat.factorial_succ]
  push_cast
  have hF : ((a+b).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hC : (Nat.choose (a+b) a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (show a ≤ a+b by omega)).ne'
  field_simp [hF,hC]
  nlinarith [heR]
def genusBetaSum (g : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (g-1), factorialBeta (2*i) (2*(g-2-i))
lemma factorialBeta_zero_left (K : ℕ) : factorialBeta 0 K = 1/(K+1 : ℕ) := by
  rw [factorialBeta_choose]
  simp
lemma factorialBeta_zero_right (K : ℕ) : factorialBeta K 0 = 1/(K+1 : ℕ) := by
  rw [factorialBeta_choose]
  simp
lemma genusBetaSum_bound_aux (N : ℕ) :
    genusBetaSum (N+3) ≤ 3/(2*(N : ℝ)+3) := by
  unfold genusBetaSum
  rw [show N+3-1=N+2 by omega,show N+3-2=N+1 by omega,
    Finset.sum_range_succ,Finset.sum_range_succ']
  simp only [mul_zero,Nat.sub_zero,Nat.sub_self,
    factorialBeta_zero_left,factorialBeta_zero_right]
  have hterm : ∀ i ∈ Finset.range N,
      factorialBeta (2*(i+1)) (2*(N+1-(i+1))) ≤
        1/((2*(N : ℝ)+2)*(2*N+3)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : 2*(i+1)+2*(N+1-(i+1))=2*N+2 := by omega
    rw [factorialBeta_choose,he]
    have hC := choose_interior_lower (2*N+2) (2*(i+1)) (by omega) (by omega)
    have hCR : (2*(N : ℝ)+2) ≤ ((2*N+2).choose (2*(i+1)) : ℝ) := by exact_mod_cast hC
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  simp only [Nat.add_sub_add_right,mul_one_div] at hsum
  push_cast
  rw [show (2 : ℝ)*(N+1)+1=2*N+3 by ring]
  calc
    _ ≤ (N : ℝ)/((2*N+2)*(2*N+3))+2/(2*N+3) := by
      nlinarith only [hsum, show (2 : ℝ)/(2*N+3) = 1/(2*N+3)+1/(2*N+3) by ring]
    _ ≤ 3/(2*N+3) := by
      have h₂ : (0 : ℝ) < 2*N+2 := by positivity
      have h₃ : (0 : ℝ) < 2*N+3 := by positivity
      field_simp [h₂.ne',h₃.ne']
      nlinarith
lemma genusBetaSum_bound (g : ℕ) (hg : 2 ≤ g) :
    genusBetaSum g ≤ 3/(2*(g : ℝ)-3) := by
  by_cases h2 : g = 2
  · subst g
    norm_num [genusBetaSum,factorialBeta]
  · have hg3 : 3 ≤ g := by omega
    have he : g = (g-3)+3 := by omega
    have hcast : (g : ℝ) = (g-3 : ℕ)+3 := by exact_mod_cast he
    have hh := genusBetaSum_bound_aux (g-3)
    rw [← he] at hh
    convert hh using 1 <;> rw [hcast] <;> congr 1 <;> ring
lemma factorial_convolution (a b N : ℕ) :
    (∑ m ∈ Finset.range (N+1), (N.choose m : ℝ)*
      ((a+m).factorial : ℝ)*(b+(N-m)).factorial/(a+b+N+2).factorial) =
      factorialBeta a b/(a+b+N+2 : ℕ) := by
  have hsum : (∑ m ∈ Finset.range (N+1), (N.choose m : ℝ)*
      ((a+m).factorial : ℝ)*(b+(N-m)).factorial/(a+b+N+2).factorial) =
      (∑ m ∈ Finset.range (N+1), (N.choose m : ℝ)*
        factorialBeta (a+m) (b+(N-m)))/(a+b+N+2 : ℕ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_range.mp hm
    have he : a+m+(b+(N-m))+1 = a+b+N+1 := by omega
    unfold factorialBeta
    rw [he,show a+b+N+2=(a+b+N+1)+1 by omega,Nat.factorial_succ]
    push_cast
    field_simp
  rw [hsum,factorialBeta_convolution]
/-- The complete combinatorial majorant for the actual separating DVV weights. -/
def primitiveSeparatingWeight (g n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (g-1), ∑ m ∈ Finset.range n,
    ((n-1).choose m : ℝ)*((2*i+m).factorial : ℝ)*
      (2*(g-2-i)+(n-1-m)).factorial /
      (6*(complexity g n-1).factorial)
lemma primitiveSeparatingWeight_formula (g n : ℕ) (hg : 2 ≤ g) (hn : 1 ≤ n) :
    primitiveSeparatingWeight g n =
      genusBetaSum g/(6*(complexity g n-1 : ℕ)) := by
  unfold primitiveSeparatingWeight genusBetaSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hN : n = (n-1)+1 := by omega
  have he : 2*i+2*(g-2-i)+(n-1)+2 = complexity g n-1 := by
    unfold complexity
    omega
  have hconv := factorial_convolution (2*i) (2*(g-2-i)) (n-1)
  rw [he,← hN] at hconv
  have heq :
      (∑ m ∈ Finset.range n, ((n-1).choose m : ℝ)*
        ((2*i+m).factorial : ℝ)*(2*(g-2-i)+(n-1-m)).factorial /
          (6*(complexity g n-1).factorial)) =
      (∑ m ∈ Finset.range n, ((n-1).choose m : ℝ)*
        ((2*i+m).factorial : ℝ)*(2*(g-2-i)+(n-1-m)).factorial /
          (complexity g n-1).factorial)/6 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [heq,hconv]
  ring
lemma primitiveSeparatingWeight_bound (g n : ℕ) (hg : 2 ≤ g) (hn : 1 ≤ n)
    (hnmax : n ≤ 3*g-3) :
    primitiveSeparatingWeight g n ≤
      2/(((complexity g n : ℝ)-1)*((complexity g n : ℝ)-2)) := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmaxR : (n : ℝ) ≤ 3*(g : ℝ)-3 := by
    have he : (3*g-3 : ℕ) = 3*(g-1) := by omega
    rw [he] at hnmax
    have hh : ((g-1 : ℕ) : ℝ) = (g : ℝ)-1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have h' : (n : ℝ) ≤ 3*((g-1 : ℕ) : ℝ) := by exact_mod_cast hnmax
    rw [hh] at h'
    linarith
  have hc : (complexity g n : ℝ) = 2*(g : ℝ)+n-2 := by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have h₁ : (0 : ℝ) < (complexity g n : ℝ)-1 := by rw [hc]; linarith
  have h₂ : (0 : ℝ) < (complexity g n : ℝ)-2 := by rw [hc]; linarith
  have hG : (0 : ℝ) < 2*(g : ℝ)-3 := by linarith
  have hcast : ((complexity g n-1 : ℕ) : ℝ) = (complexity g n : ℝ)-1 := by
    rw [Nat.cast_sub (by unfold complexity; omega)]; norm_num
  rw [primitiveSeparatingWeight_formula g n hg hn,hcast]
  calc
    _ ≤ (3/(2*(g : ℝ)-3))/(6*((complexity g n : ℝ)-1)) :=
      div_le_div_of_nonneg_right (genusBetaSum_bound g hg) (by positivity)
    _ ≤ _ := by
      field_simp [h₁.ne',h₂.ne',hG.ne']
      rw [hc]
      nlinarith
end WP
