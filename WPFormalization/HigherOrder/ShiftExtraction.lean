import WPFormalization.HigherOrder.ShiftCoefficientBounds
import Mathlib.RingTheory.PowerSeries.Exp

/-! Exact finite coefficient extraction for the actual complexity substitution, and its normalized exponential coefficient majorant. These are algebraic identities and bounds, with no convergence or hierarchy remainder assumption. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma coeff_shiftVariable_pow (c:ℝ) (i K:ℕ) :
    PowerSeries.coeff K ((shiftVariable c)^i)=
      if i ≤ K then PowerSeries.coeff (K-i) (((1-C c*PowerSeries.X : Series)⁻¹)^i) else 0 := by
  unfold shiftVariable
  rw [mul_pow,PowerSeries.coeff_X_pow_mul']

lemma complexityShift_coeff_sum (c:ℝ) (f:Series) (K:ℕ) :
    PowerSeries.coeff K (complexityShift c f)=
      ∑i∈Finset.range (K+1),PowerSeries.coeff i f*
        PowerSeries.coeff (K-i) (((1-C c*PowerSeries.X : Series)⁻¹)^i) := by
  unfold complexityShift
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (shiftVariable_constant c))]
  have hs : Function.support (fun i:ℕ=>PowerSeries.coeff i f • PowerSeries.coeff K ((shiftVariable c)^i))⊆
      (Finset.range (K+1):Set ℕ) := by
    intro i hi
    by_contra hn
    have hiK : K < i := by
      have hh : ¬ i < K+1 := by simpa only [Finset.mem_coe,Finset.mem_range] using hn
      omega
    have hz : PowerSeries.coeff K ((shiftVariable c)^i)=0 := by
      rw [coeff_shiftVariable_pow,if_neg (by omega)]
    exact hi (by simp [hz])
  rw [finsum_eq_sum_of_support_subset _ hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_shiftVariable_pow,if_pos (by have hi':=Finset.mem_range.mp hi;omega)]
  rfl

lemma complexityShift_coeff_sum_positive (c:ℝ) (f:Series) (K:ℕ) (hK:1 ≤ K) :
    PowerSeries.coeff K (complexityShift c f)=
      ∑i∈Finset.range (K+1),if 1 ≤ i then PowerSeries.coeff i f*
        (Nat.choose (K-1) (i-1):ℝ)*c^(K-i) else 0 := by
  rw [complexityShift_coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hi0 : i=0
  · subst i
    simp only [pow_zero,PowerSeries.coeff_one,Nat.sub_zero,if_neg (by omega : ¬K=0),mul_zero,
      show ¬1 ≤ 0 by omega,ite_false]
  · have hiK : i ≤ K:=by have hi':=Finset.mem_range.mp hi;omega
    rw [if_pos (by omega : 1 ≤ i),inverse_linear_pow_coeff c i (K-i) (by omega)]
    have hn : i+(K-i)-1=K-1:=by omega
    rw [hn]
    have hc : Nat.choose (K-1) (K-i)=Nat.choose (K-1) (i-1) :=
      Nat.choose_symm_of_eq_add (by omega)
    rw [hc]
    ring
lemma inverse_linear_pow_coeff_normalized_all (c S:ℝ) (a q j:ℕ)
    (haj:a+q ≤ j) (hc:|c| ≤ j) (hS:(j:ℝ) ≤ S) :
    |PowerSeries.coeff q (((1-C c*PowerSeries.X : Series)⁻¹)^a)| ≤ S^(2*q)/(q.factorial:ℝ) := by
  have hS0 : 0≤S:=(Nat.cast_nonneg j).trans hS
  by_cases ha : a=0
  · subst a
    cases q with
    | zero => simp
    | succ q => simp only [pow_zero,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false,abs_zero];positivity
  · exact inverse_linear_pow_coeff_normalized c S a q j (by omega) haj hc hS

lemma complexityShift_coeff_scaled_bound (c S:ℝ) (f:Series) (e:ℕ→ℝ) (K j:ℕ)
    (hK:K ≤ j) (hc:|c| ≤ j) (hS:(j:ℝ) ≤ S) (he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i ≤ K→|PowerSeries.coeff i f| ≤ e i*S^(2*i)) :
    |PowerSeries.coeff K (complexityShift c f)| ≤
      S^(2*K)*(∑i∈Finset.range (K+1),e i/((K-i).factorial:ℝ)) := by
  have hS0 : 0 ≤ S:=(Nat.cast_nonneg j).trans hS
  rw [complexityShift_coeff_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑i∈Finset.range (K+1),e i*S^(2*K)/((K-i).factorial:ℝ) := by
         apply Finset.sum_le_sum
         intro i hi
         have hiK : i ≤ K:=by have h:=Finset.mem_range.mp hi;omega
         rw [abs_mul]
         have hd:=inverse_linear_pow_coeff_normalized_all c S i (K-i) j (by omega) hc hS
         apply (mul_le_mul (hf i hiK) hd (abs_nonneg _) (mul_nonneg (he i) (pow_nonneg hS0 _))).trans_eq
         have hp : S^(2*i)*S^(2*(K-i))=S^(2*K):=by rw [←pow_add];congr 1;omega
         calc _ = e i*(S^(2*i)*S^(2*(K-i)))/((K-i).factorial:ℝ):=by ring
              _ = _:=by rw [hp]
       _ = _ := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i hi;ring

lemma exp_series_convolution_coeff (e:ℕ→ℝ) (K:ℕ) :
    PowerSeries.coeff K ((PowerSeries.exp ℝ)*PowerSeries.mk e)=
      ∑i∈Finset.range (K+1),e i/((K-i).factorial:ℝ) := by
  rw [mul_comm,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk,PowerSeries.coeff_exp]
  norm_num
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma complexityShift_coeff_exponential_majorant (c S:ℝ) (f:Series) (e:ℕ→ℝ) (K j:ℕ)
    (hK:K ≤ j) (hc:|c| ≤ j) (hS:(j:ℝ) ≤ S) (he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i ≤ K→|PowerSeries.coeff i f| ≤ e i*S^(2*i)) :
    |PowerSeries.coeff K (complexityShift c f)| ≤
      S^(2*K)*PowerSeries.coeff K ((PowerSeries.exp ℝ)*PowerSeries.mk e) := by
  rw [exp_series_convolution_coeff]
  exact complexityShift_coeff_scaled_bound c S f e K j hK hc hS he hf
end WP.HigherOrder
