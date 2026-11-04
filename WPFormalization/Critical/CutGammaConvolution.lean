import Mathlib

/-! Exact stable-complexity allocation sums and their Gamma convolution bound
for Appendix G. Every ordered nonnegative allocation is included; no volume
or geometric counting assumption occurs in this module. -/

noncomputable section
namespace WP.Critical
open Finset

lemma cut_choose_ge_degree (n k : ℕ) (hk : 1≤k) (hkn : k<n) : n≤n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases hk1 : k=1
    · subst k
      simp
    by_cases hkn' : k=n
    · subst k
      rw [←Nat.choose_symm (by omega),show n+1-n=1 by omega,Nat.choose_one_right]
    have hk0 : 0<k := by omega
    rw [Nat.choose_succ_left n k hk0]
    have h1 := ih (k-1) (by omega) (by omega)
    have h2 := ih k hk (by omega)
    omega

lemma cut_factorial_split_ratio (n k : ℕ) (hk : k≤n) :
    ((k.factorial:ℝ)*(n-k).factorial)/(n.factorial:ℝ) = ((n.choose k:ℕ):ℝ)⁻¹ := by
  have he := Nat.choose_mul_factorial_mul_factorial hk
  have hp : (0:ℝ)<(n.choose k:ℕ) := by exact_mod_cast Nat.choose_pos hk
  have hf : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [inv_eq_one_div]
  apply (div_eq_div_iff hf.ne' hp.ne').mpr
  norm_cast
  nlinarith only [he]

lemma cut_factorial_convolution_bound (n : ℕ) :
    (∑k∈range (n+1),(k.factorial:ℝ)*(n-k).factorial) ≤ 3*(n.factorial:ℝ) := by
  by_cases hn : n=0
  · subst n
    norm_num
  have hnp : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnf : 0<(n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hm (k:ℕ) (hk:k∈range (n-1)) :
      (((k+1).factorial:ℝ)*(n-(k+1)).factorial)/(n.factorial:ℝ) ≤ 1/(n:ℝ) := by
    have hkn : k+1<n := by have := mem_range.mp hk;omega
    rw [cut_factorial_split_ratio n (k+1) hkn.le]
    have hc := cut_choose_ge_degree n (k+1) (by omega) hkn
    rw [one_div]
    exact inv_anti₀ hnp (by exact_mod_cast hc)
  have hdecomp : (∑k∈range (n+1),((k.factorial:ℝ)*(n-k).factorial)/(n.factorial:ℝ)) =
      2+∑k∈range (n-1),(((k+1).factorial:ℝ)*(n-(k+1)).factorial)/(n.factorial:ℝ) := by
    rw [sum_range_succ]
    have hn' : n=(n-1)+1 := by omega
    have hi := sum_range_succ' (fun k=>((k.factorial:ℝ)*(n-k).factorial)/(n.factorial:ℝ)) (n-1)
    rw [←hn'] at hi
    rw [hi]
    simp only [Nat.factorial_zero,Nat.sub_zero,mul_one,one_mul,
      Nat.sub_self,Nat.cast_one,div_self hnf.ne']
    ring

  have hsum : (∑k∈range (n+1),((k.factorial:ℝ)*(n-k).factorial)/(n.factorial:ℝ)) ≤3 := by
    rw [hdecomp]
    have hu := sum_le_sum hm
    simp only [sum_const,card_range,nsmul_eq_mul] at hu
    have hncast : ((n-1:ℕ):ℝ)≤(n:ℝ) := by exact_mod_cast Nat.sub_le n 1
    have he : ((n-1:ℕ):ℝ)*(1/(n:ℝ))≤1 := by
      have := mul_le_mul_of_nonneg_right hncast (inv_nonneg.mpr hnp.le)
      simpa only [one_div,mul_inv_cancel₀ hnp.ne'] using this
    linarith
  rw [←sum_div] at hsum
  exact (div_le_iff₀ hnf).mp hsum

end WP.Critical

namespace WP.Critical
open Finset

/-- The exact positive-complexity Gamma allocation sum, after writing h_i=j_i+1.
The recursive convolution enumerates every ordered nonnegative tuple with total N. -/
def cutStableConvolution : ℕ → ℕ → ℝ
  | 0,N => if N=0 then 1 else 0
  | w+1,N => ∑j∈range (N+1),(j.factorial:ℝ)*cutStableConvolution w (N-j)

lemma cutStableConvolution_nonneg (w N : ℕ) : 0≤cutStableConvolution w N := by
  induction w generalizing N with
  | zero => simp only [cutStableConvolution];split_ifs <;> norm_num
  | succ w ih => exact sum_nonneg (fun j _=>mul_nonneg (Nat.cast_nonneg _) (ih _))

lemma cutStableConvolution_one (N : ℕ) : cutStableConvolution 1 N=(N.factorial:ℝ) := by
  simp only [cutStableConvolution]
  rw [sum_eq_single N]
  · simp
  · intro j hj hne
    have hjN : j<N := by have := mem_range.mp hj;omega
    have hsub : N-j≠0 := by omega
    simp only [hsub,ite_false,mul_zero]
  · intro hn
    exact (hn (mem_range.mpr (by omega))).elim

lemma cutStableConvolution_two (N : ℕ) :
    cutStableConvolution 2 N=∑j∈range (N+1),(j.factorial:ℝ)*(N-j).factorial := by
  change (∑j∈range (N+1),(j.factorial:ℝ)*cutStableConvolution 1 (N-j))=_
  simp only [cutStableConvolution_one]

lemma cutStableConvolution_bound (w N : ℕ) :
    cutStableConvolution w N ≤ (3:ℝ)^w*(N.factorial:ℝ) := by
  induction w generalizing N with
  | zero =>
    simp only [cutStableConvolution,pow_zero,one_mul]
    split_ifs with hN
    · subst N;norm_num
    · positivity
  | succ w ih =>
    calc
      _ ≤ ∑j∈range (N+1),(j.factorial:ℝ)*((3:ℝ)^w*(N-j).factorial) :=
        sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (ih _) (Nat.cast_nonneg _))
      _ = (3:ℝ)^w*(∑j∈range (N+1),(j.factorial:ℝ)*(N-j).factorial) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
      _ ≤ (3:ℝ)^w*(3*(N.factorial:ℝ)) :=
        mul_le_mul_of_nonneg_left (cut_factorial_convolution_bound N) (by positivity)
      _ = (3:ℝ)^(w+1)*(N.factorial:ℝ) := by rw [pow_succ];ring

/-- The stable-vertex allocation in the original positive complexities h_i>=1.
The finite reindexing h_i=j_i+1 leaves total degree H-w. -/
def cutStableGammaSum (w H : ℕ) : ℝ :=
  if w≤H then cutStableConvolution w (H-w) else 0

lemma cutStableGammaSum_bound (w H : ℕ) (hwH : w≤H) :
    cutStableGammaSum w H ≤ (3:ℝ)^w*Real.Gamma ((H-w:ℕ)+1:ℕ) := by
  rw [cutStableGammaSum,if_pos hwH,Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial]
  simpa only [Nat.add_sub_cancel] using cutStableConvolution_bound w (H-w)

end WP.Critical
namespace WP.Critical
open Finset

/-- The factorial series whose w-th power enumerates ordered stable complexities. -/
def cutFactorialSeries : PowerSeries ℝ := PowerSeries.mk fun j=>(j.factorial:ℝ)

lemma cutStableConvolution_eq_coeff (w N : ℕ) :
    cutStableConvolution w N = PowerSeries.coeff N (cutFactorialSeries^w) := by
  induction w generalizing N with
  | zero => simp [cutStableConvolution,PowerSeries.coeff_one]
  | succ w ih =>
    rw [pow_succ',PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    change (∑j∈range (N+1),(j.factorial:ℝ)*cutStableConvolution w (N-j))=_
    apply sum_congr rfl
    intro j hj
    rw [ih]
    simp only [cutFactorialSeries,PowerSeries.coeff_mk]

/-- The exact sum over every ordered nonnegative allocation of total N. In the
paper the positive stable complexities are h_i=l_i+1 and H=N+w. -/
lemma cutStable_factorial_allocation_bound (w N : ℕ) :
    (∑l∈finsuppAntidiag (range w) N, ∏i∈range w, (l i).factorial:ℝ) ≤
      (3:ℝ)^w*(N.factorial:ℝ) := by
  have he := cutStableConvolution_eq_coeff w N
  rw [PowerSeries.coeff_pow] at he
  simp only [cutFactorialSeries,PowerSeries.coeff_mk] at he
  rw [←he]
  exact cutStableConvolution_bound w N

lemma cutStable_gamma_allocation_bound (w N : ℕ) :
    (∑l∈finsuppAntidiag (range w) N,
      ∏i∈range w, Real.Gamma ((l i:ℝ)+1)) ≤
      (3:ℝ)^w*Real.Gamma ((N:ℝ)+1) := by
  simp only [Real.Gamma_nat_eq_factorial]
  exact cutStable_factorial_allocation_bound w N

end WP.Critical
