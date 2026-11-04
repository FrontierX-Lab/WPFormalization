import WPFormalization.Analysis.KernelPolynomialTails

/-! Uniform finite-prefix errors for an arbitrary polynomially bounded kernel summand. -/
noncomputable section
open Set
namespace WP.Analysis
lemma weighted_polynomial_prefix_error_uniform (q k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ Y∈Icc (0:ℝ) y₀,∀ D : ℕ,∀ K : ℝ,0 ≤ K →
      ∀ f : ℕ→ℝ,∀ B : ℝ,(∀ l,|f l| ≤ K*((D:ℝ)+l+1)^q) →
      HasSum (fun l => weight Y l*f l) B → ∀ N : ℕ,
        |(∑ l∈Finset.range N,weight Y l*f l)-B| ≤ K*C*((D:ℝ)+1)^q/((N:ℝ)+1)^k := by
  obtain ⟨C,hC,hTail⟩ := weight_polynomial_tail_uniform q k
  refine ⟨C,hC,?_⟩
  intro Y hY D K hK f B hf hfull N
  let F : ℕ→ℝ := fun l => weight Y l*f l
  have hpre : HasSum (fun l : ℕ => if l<N then F l else 0) (∑ l∈Finset.range N,F l) := by
    have he : HasSum (fun l : ℕ => if l<N then F l else 0)
        (∑ l∈Finset.range N,if l<N then F l else 0) :=
      hasSum_sum_of_ne_finset_zero (by
        intro l hl
        simp only [Finset.mem_range] at hl
        rw [if_neg hl])
    simpa only [Finset.sum_ite_of_true (fun l hl => Finset.mem_range.mp hl)] using he
  have htail : HasSum (fun l : ℕ => if N ≤ l then F l else 0) (B-∑ l∈Finset.range N,F l) := by
    have heq : (fun l : ℕ => F l-(if l<N then F l else 0))=(fun l => if N ≤ l then F l else 0) := by
      funext l
      by_cases hl : l<N
      · simp only [if_pos hl,if_neg (by omega : ¬N ≤ l),sub_self]
      · simp only [if_neg hl,if_pos (by omega : N ≤ l),sub_zero]
    rw [←heq]
    exact hfull.sub hpre
  have hpoint (l : ℕ) : |(if N ≤ l then F l else 0)| ≤
      K*(if N ≤ l then ((D:ℝ)+l+1)^q*weight Y l else 0) := by
    by_cases hl : N ≤ l
    · rw [if_pos hl,if_pos hl]
      dsimp [F]
      rw [abs_mul,abs_of_nonneg (weight_nonneg Y hY l)]
      have hm := mul_le_mul_of_nonneg_left (hf l) (weight_nonneg Y hY l)
      convert hm using 1 <;> ring
    · rw [if_neg hl,if_neg hl,abs_zero,mul_zero]
  have hn := htail.summable.abs
  have ht := hTail Y hY D N
  have hnorm : Summable (fun l : ℕ => ‖if N ≤ l then F l else 0‖) := by
    simpa only [Real.norm_eq_abs] using hn
  rw [abs_sub_comm,←htail.tsum_eq]
  calc
    _ ≤ ∑' l : ℕ,|(if N ≤ l then F l else 0)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' l : ℕ,K*(if N ≤ l then ((D:ℝ)+l+1)^q*weight Y l else 0) :=
      hn.tsum_le_tsum hpoint (ht.1.mul_left K)
    _ = K*∑' l : ℕ,if N ≤ l then ((D:ℝ)+l+1)^q*weight Y l else 0 := tsum_mul_left
    _ ≤ K*(C*((D:ℝ)+1)^q/((N:ℝ)+1)^k) := mul_le_mul_of_nonneg_left ht.2 hK
    _ = _ := by ring
end WP.Analysis
