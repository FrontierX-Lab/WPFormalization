import WPFormalization.HigherOrder.FiniteGevreyOne
import WPFormalization.HigherOrder.EndpointZBounds
import WPFormalization.HigherOrder.BernoulliCoefficientBounds
import WPFormalization.HigherOrder.ShiftExtraction

/-! The canonical endpoint formal series and its logarithm satisfy factorial coefficient bounds at each fixed marking count. This proves only formal Gevrey estimates, not the growing-order matching with the actual geometric endpoint. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma half_choose_abs_le_one (n : ℕ) : |Ring.choose (1/2:ℝ) n| ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he := Ring.choose_smul_choose (1/2:ℝ) (show n ≤ n+1 by omega)
    rw [Nat.choose_succ_self_right,nsmul_eq_mul,show n+1-n=1 by omega,Ring.choose_one_right] at he
    push_cast at he
    have hnp : (0:ℝ)<n+1 := by positivity
    have hab : |(1/2:ℝ)-(n:ℝ)| ≤ (n:ℝ)+1 := by
      apply abs_le.mpr
      constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) n]
    have he' := congrArg abs he
    rw [abs_mul,abs_mul,abs_of_pos hnp] at he'
    have hh := mul_le_mul ih hab (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    norm_num only [one_mul] at hh
    nlinarith

lemma gammaRatioSeries_factorial_bound (n : ℕ) :
    |PowerSeries.coeff n (gammaRatioSeries (3/2))| ≤
      Real.exp 14*(56:ℝ)^n*(n.factorial:ℝ) := by
  simpa only [gammaRatioSeries,show (8:ℝ)*7=56 by norm_num] using
    finiteExp_gevrey_one (gammaRatioLog (3/2)) 14 7 (by norm_num) (by norm_num)
      gammaRatioLog_factorial_bound n

/-- A finite coefficient bound; no analytic remainder is included. -/
def HasFactorialBound (f : Series) : Prop :=
  ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ n : ℕ,
    |PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)
lemma hasFactorialBound_mul {f g : Series}
    (hf : HasFactorialBound f) (hg : HasFactorialBound g) : HasFactorialBound (f*g) := by
  obtain ⟨C,B,hC,hB,hf⟩ := hf
  obtain ⟨D,E,hD,hE,hg⟩ := hg
  exact ⟨C*D,2*(B+E),by positivity,by positivity,
    gevrey_one_mul_combine f g C D B E hC hD hB hE hf hg⟩
lemma hasFactorialBound_one : HasFactorialBound (1:Series) := by
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  intro n
  by_cases hn : n=0
  · subst n;simp
  · simp only [PowerSeries.coeff_one,if_neg hn,abs_zero,one_pow,one_mul]
    positivity
lemma hasFactorialBound_prod {ι : Type*} (s : Finset ι) (f : ι→Series)
    (hf : ∀ i∈s,HasFactorialBound (f i)) : HasFactorialBound (∏ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasFactorialBound_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact hasFactorialBound_mul (hf i (Finset.mem_insert_self i s))
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
lemma hasFactorialBound_inverse_linear (c : ℝ) :
    HasFactorialBound ((1-C c*PowerSeries.X : Series)⁻¹) := by
  refine ⟨1,|c|,by norm_num,abs_nonneg _,?_⟩
  intro n
  have he := inverse_linear_pow_coeff c 1 n (by omega)
  simp only [pow_one,show 1+n-1=n by omega,Nat.choose_self,Nat.cast_one,one_mul] at he
  rw [he,abs_pow,one_mul]
  exact le_mul_of_one_le_right (pow_nonneg (abs_nonneg c) n)
    (show (1:ℝ)≤n.factorial by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n))

lemma hasFactorialBound_linear (c : ℝ) :
    HasFactorialBound (1+C c*PowerSeries.X : Series) := by
  refine ⟨1+|c|,1,by positivity,by norm_num,?_⟩
  intro n
  by_cases hn0 : n=0
  · subst n
    simp only [map_add,PowerSeries.coeff_one,ite_true,PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X,show ¬(0:ℕ)=1 by omega,ite_false,mul_zero,add_zero,
      abs_one,one_pow,Nat.factorial_zero,Nat.cast_one,mul_one]
    linarith [abs_nonneg c]
  · by_cases hn1 : n=1
    · subst n
      simp only [map_add,PowerSeries.coeff_one,show ¬(1:ℕ)=0 by omega,ite_false,
        PowerSeries.coeff_C_mul,PowerSeries.coeff_X,ite_true,mul_one,zero_add,
        one_pow,Nat.factorial_one,Nat.cast_one,mul_one]
      linarith [abs_nonneg c]
    · simp only [map_add,PowerSeries.coeff_one,if_neg hn0,
        PowerSeries.coeff_C_mul,PowerSeries.coeff_X,if_neg hn1,mul_zero,
        add_zero,abs_zero,one_pow,mul_one]
      positivity
lemma hasFactorialBound_half_binomial_rescale (c : ℝ) :
    HasFactorialBound (PowerSeries.rescale c (binomial (1/2))) := by
  refine ⟨1,|c|,by norm_num,abs_nonneg _,?_⟩
  intro n
  rw [PowerSeries.coeff_rescale,binomial,PowerSeries.binomialSeries_coeff,
    smul_eq_mul,mul_one,abs_mul,abs_pow,one_mul]
  calc
    _ ≤ |c|^n*1 := mul_le_mul_of_nonneg_left (half_choose_abs_le_one n) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (show (1:ℝ)≤n.factorial by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)) (by positivity)
lemma hasFactorialBound_endpointInsertion (p : ℕ) : HasFactorialBound (endpointInsertion p) := by
  unfold endpointInsertion
  apply hasFactorialBound_mul (hasFactorialBound_half_binomial_rescale p)
  apply hasFactorialBound_prod
  intro i hi
  apply hasFactorialBound_mul (hasFactorialBound_linear (4*(i:ℝ)/5))
  convert hasFactorialBound_inverse_linear (-(i:ℝ)) using 1
  simp only [map_neg,neg_mul,sub_neg_eq_add]
lemma hasFactorialBound_endpointAtH₀ (p : ℕ) : HasFactorialBound (endpointAtH₀ p) := by
  unfold endpointAtH₀
  apply hasFactorialBound_mul
  · apply hasFactorialBound_mul
    · apply hasFactorialBound_mul
      · exact ⟨1,64*Real.exp 2,by norm_num,by positivity,by simpa using endpointZ_factorial_bound⟩
      · exact ⟨Real.exp 14,56,by positivity,by norm_num,gammaRatioSeries_factorial_bound⟩
    · exact hasFactorialBound_endpointInsertion p
  · convert hasFactorialBound_inverse_linear (-(4/5:ℝ)) using 1
    simp only [map_neg,neg_mul,sub_neg_eq_add]

lemma hasFactorialBound_complexityShift (c : ℝ) {f : Series}
    (hf : HasFactorialBound f) : HasFactorialBound (complexityShift c f) := by
  obtain ⟨C,B,hC,hB,hf⟩ := hf
  let A := B+|c|+1
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hBA : B ≤ A := by dsimp [A];linarith [abs_nonneg c]
  have hcA : |c| ≤ A := by dsimp [A];linarith
  refine ⟨C,4*A,hC,by positivity,?_⟩
  intro n
  by_cases hn0 : n=0
  · subst n
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff,complexityShift_constant,
      pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one] using hf 0
  have hn : 1 ≤ n := by omega
  have ht (i : ℕ) (hi : i∈Finset.range (n+1)) :
      |if 1 ≤ i then PowerSeries.coeff i f*(Nat.choose (n-1) (i-1):ℝ)*c^(n-i) else 0| ≤
        C*(2*A)^n*(n.factorial:ℝ) := by
    by_cases hi1 : 1 ≤ i
    · rw [if_pos hi1,abs_mul,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg (Nat.choose (n-1) (i-1)) : (0:ℝ) ≤ _) ]
      have hin : i ≤ n := by have := Finset.mem_range.mp hi;omega
      have hfac : (i.factorial:ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hin
      have hchoose : (Nat.choose (n-1) (i-1):ℝ) ≤ (2:ℝ)^n := by
        have hc : (Nat.choose (n-1) (i-1):ℝ) ≤ (2:ℝ)^(n-1) := by
          exact_mod_cast Nat.choose_le_two_pow (n-1) (i-1)
        exact hc.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.sub_le n 1))
      calc
        _ ≤ (C*B^i*(i.factorial:ℝ))*(2:ℝ)^n*|c|^(n-i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (hf i) hchoose (Nat.cast_nonneg _) (by positivity)) (by positivity)
        _ ≤ (C*A^i*(n.factorial:ℝ))*(2:ℝ)^n*A^(n-i) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hB hBA i) hC) hfac (by positivity) (by positivity)
          · exact pow_le_pow_left₀ (abs_nonneg c) hcA (n-i)
          · positivity
          · positivity
        _ = _ := by
          have hp : A^i*A^(n-i)=A^n := by rw [←pow_add,Nat.add_sub_of_le hin]
          rw [mul_pow]
          calc
            _ = C*(2:ℝ)^n*(A^i*A^(n-i))*(n.factorial:ℝ) := by ring
            _ = _ := by rw [hp];ring
    · rw [if_neg hi1,abs_zero]
      positivity
  rw [complexityShift_coeff_sum_positive c f n hn]
  calc
    _ ≤ ∑ i∈Finset.range (n+1),
      |if 1 ≤ i then PowerSeries.coeff i f*(Nat.choose (n-1) (i-1):ℝ)*c^(n-i) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i∈Finset.range (n+1),C*(2*A)^n*(n.factorial:ℝ) := Finset.sum_le_sum ht
    _ = ((n:ℝ)+1)*(C*(2*A)^n*(n.factorial:ℝ)) := by simp
    _ ≤ (2:ℝ)^n*(C*(2*A)^n*(n.factorial:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (show n < (2:ℕ)^n from Nat.lt_two_pow_self)
    _ = _ := by
      have hp : (2:ℝ)^n*(2*A)^n=(4*A)^n := by rw [←mul_pow];congr 1;ring
      calc
        _ = C*((2:ℝ)^n*(2*A)^n)*(n.factorial:ℝ) := by ring
        _ = _ := by rw [hp]
lemma hasFactorialBound_finiteLog {f : Series}
    (hf : HasFactorialBound f) : HasFactorialBound (finiteLog f) := by
  obtain ⟨C,B,hC,hB,hf⟩ := hf
  exact ⟨1,8*(C+1)*(B+1),by norm_num,by positivity,
    by simpa only [one_mul] using finiteLog_gevrey_one f C B hC hB hf⟩

theorem endpointLogCoefficient_factorial_bound (p : ℕ) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ n : ℕ,
      |endpointLogCoefficient p n| ≤ C*B^n*(n.factorial:ℝ) := by
  obtain ⟨C,B,hC,hB,hf⟩ := hasFactorialBound_finiteLog
    (hasFactorialBound_complexityShift (p:ℝ) (hasFactorialBound_endpointAtH₀ p))
  refine ⟨C+1,B+1,by positivity,by positivity,?_⟩
  intro n
  apply (hf n).trans
  change C*B^n*(n.factorial:ℝ) ≤ _
  gcongr <;> linarith

end WP.HigherOrder
