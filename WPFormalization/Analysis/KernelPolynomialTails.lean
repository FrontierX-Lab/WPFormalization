import WPFormalization.Analysis.UniformKernelMoments

/-! Polynomial tails and finite-prefix moments of the actual nonnegative kernel weights, uniform on the closed parameter interval. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP.Analysis
lemma weight_polynomial_tail_uniform (q k : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ D N : ℕ,
      Summable (fun l : ℕ => if N ≤ l then ((D:ℝ)+l+1)^q*weight Y l else 0) ∧
      ∑' l : ℕ, (if N ≤ l then ((D:ℝ)+l+1)^q*weight Y l else 0) ≤
        C*((D:ℝ)+1)^q/((N:ℝ)+1)^k := by
  obtain ⟨M,hM⟩ := uniform_kernel_moments.2 (q+k)
  refine ⟨max 1 M,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro Y hY D N
  let c : ℝ := ((D:ℝ)+1)^q/((N:ℝ)+1)^k
  have hc : 0 ≤ c := by dsimp [c];positivity
  have hpoint (l : ℕ) : (if N ≤ l then ((D:ℝ)+l+1)^q*weight Y l else 0) ≤
      c*((1+(l:ℝ))^(q+k)*weight Y l) := by
    by_cases hl : N ≤ l
    · rw [if_pos hl]
      have hNl : (N:ℝ)+1 ≤ 1+(l:ℝ) := by exact_mod_cast (show N+1 ≤ 1+l by omega)
      have hbase : (D:ℝ)+l+1 ≤ ((D:ℝ)+1)*(1+(l:ℝ)) := by
        nlinarith [mul_nonneg (show (0:ℝ)≤D from Nat.cast_nonneg _) (show (0:ℝ)≤l from Nat.cast_nonneg _)]
      have hp := pow_le_pow_left₀ (show (0:ℝ)≤(D:ℝ)+l+1 by positivity) hbase q
      have hn := pow_le_pow_left₀ (show (0:ℝ)≤(N:ℝ)+1 by positivity) hNl k
      have hprod := mul_le_mul hp hn (by positivity) (by positivity)
      have hprod' : (((D:ℝ)+l+1)^q*weight Y l)*((N:ℝ)+1)^k ≤
          ((D:ℝ)+1)^q*((1+(l:ℝ))^(q+k)*weight Y l) := by
        have hi := mul_le_mul_of_nonneg_right hprod (weight_nonneg Y hY l)
        simpa only [mul_pow,pow_add,mul_assoc,mul_left_comm,mul_comm] using hi
      have hden : 0<((N:ℝ)+1)^k := by positivity
      dsimp [c]
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hden).2 hprod'
    · rw [if_neg hl]
      exact mul_nonneg hc (mul_nonneg (by positivity) (weight_nonneg Y hY l))
  have hs : Summable (fun l : ℕ => if N ≤ l then ((D:ℝ)+l+1)^q*weight Y l else 0) :=
    Summable.of_nonneg_of_le (fun l => by
      split_ifs
      · exact mul_nonneg (by positivity) (weight_nonneg Y hY l)
      · exact le_rfl) hpoint ((hM Y hY).1.mul_left c)
  refine ⟨hs,?_⟩
  calc _ ≤ ∑' l : ℕ, c*((1+(l:ℝ))^(q+k)*weight Y l) := hs.tsum_le_tsum hpoint ((hM Y hY).1.mul_left c)
       _ = c*∑' l : ℕ, (1+(l:ℝ))^(q+k)*weight Y l := tsum_mul_left
       _ ≤ c*M := mul_le_mul_of_nonneg_left (hM Y hY).2 hc
       _ ≤ c*max 1 M := mul_le_mul_of_nonneg_left (le_max_right _ _) hc
       _ = _ := by dsimp [c];ring
end WP.Analysis
namespace WP.Analysis
lemma weight_polynomial_prefix_uniform (q : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ Y ∈ Set.Icc (0:ℝ) y₀, ∀ D N : ℕ,
      ∑ l ∈ Finset.range N, ((D:ℝ)+l+1)^q*weight Y l ≤ C*((D:ℝ)+1)^q := by
  obtain ⟨C,hC,hbound⟩ := weight_polynomial_tail_uniform q 0
  refine ⟨C,hC,?_⟩
  intro Y hY D N
  have hb := hbound Y hY D 0
  simp only [Nat.zero_le,ite_true,pow_zero,div_one] at hb
  exact (hb.1.sum_le_tsum _ (fun l _ => mul_nonneg (by positivity) (weight_nonneg Y hY l))).trans hb.2
end WP.Analysis
