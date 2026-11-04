import WPFormalization.Analysis.FactorialTail
import WPFormalization.Analysis.SeparatingFiniteAlgebra
/-! Finite factorial tails starting at genus two and uniform polynomial bounds for exponential tails. -/

noncomputable section
open Set
namespace WP.Analysis
lemma finite_dyadic_tail_start_two (a : ℕ→ℝ) (N : ℕ) (ha : 0≤a 2)
    (hstep : ∀ j : ℕ, 2 ≤ j → j<N → a (j+1)≤a j/2) :
    (∑ j ∈ Finset.range (N+1), if 2 ≤ j then a j else 0)≤2*a 2 := by
  cases N with
  | zero => simpa using (show (0:ℝ)≤2*a 2 by positivity)
  | succ N =>
    rw [Finset.sum_range_succ']
    simp only [show ¬2≤(0:ℕ) by omega,ite_false,add_zero]
    have hb := finite_dyadic_tail_bound (fun j => a (j+1)) N ha (by
      intro j hj hjN
      exact hstep (j+1) (by omega) (by omega))
    calc _ = ∑ j ∈ Finset.range (N+1), if 1≤j then a (j+1) else 0 := by
           apply Finset.sum_congr rfl
           intro j hj
           by_cases h : 1≤j
           · rw [if_pos h,if_pos (by omega : 2 ≤ j+1)]
           · rw [if_neg h,if_neg (by omega : ¬2 ≤ j+1)]
         _ ≤ _ := by simpa only [Nat.reduceAdd] using hb

lemma factorial_geometric_tail_start_two (Q N g : ℕ) (K : ℝ) (hK : 0≤K)
    (hN : 0<N) (hNK : 18*K≤(N:ℝ)^2) (hg : N*(Q+4)≤g) :
    (∑ j ∈ Finset.range (g/N+1), if 2 ≤ j then ((2*j+Q).factorial:ℝ)*(K/(g:ℝ)^2)^j else 0)≤
      (2*((Q+4).factorial:ℝ)*K^2)/(g:ℝ)^4 := by
  let a (j : ℕ) : ℝ := ((2*j+Q).factorial:ℝ)*(K/(g:ℝ)^2)^j
  have ha : ∀ j, 0≤a j := by intro j;dsimp [a];positivity
  have hs : ∀ j : ℕ, 2 ≤ j → j<g/N → a (j+1)≤a j/2 := by
    intro j hj hjN
    change ((2*(j+1)+Q).factorial:ℝ)*(K/(g:ℝ)^2)^(j+1)≤a j/2
    rw [factorial_quadratic_step]
    change ((2*(j:ℝ)+Q+2)*(2*(j:ℝ)+Q+1)*(K/(g:ℝ)^2))*a j≤a j/2
    have hr := factorial_tail_ratio_bound Q N g j K hK hN hNK hg (by omega)
    nlinarith [mul_le_mul_of_nonneg_right hr (ha j)]
  have hb := finite_dyadic_tail_start_two a (g/N) (ha 2) hs
  calc _ ≤ 2*a 2 := hb
       _ = _ := by dsimp [a];rw [show 2*2+Q=Q+4 by omega,div_pow];ring

lemma linear_times_exp_decay_power_bound (α : ℝ) (hα : 0<α) (g q : ℕ) (hg : 1≤g) :
    ((g:ℝ)+1)*Real.exp (-α*(g:ℝ))≤
      (2*((q+1).factorial:ℝ))/(α^(q+1)*(g:ℝ)^q) := by
  have hgR : (1:ℝ)≤g := by exact_mod_cast hg
  have hgp : (0:ℝ)<g := by linarith
  have hF : (0:ℝ)<(q+1).factorial := by positivity
  have he := (div_le_iff₀ hF).mp (Real.pow_div_factorial_le_exp (α*(g:ℝ)) (by positivity) (q+1))
  rw [mul_pow,pow_succ (g:ℝ)] at he
  have hm := mul_le_mul_of_nonneg_right (show (g:ℝ)+1≤2*(g:ℝ) by linarith)
    (show 0≤α^(q+1)*(g:ℝ)^q by positivity)
  rw [show -α*(g:ℝ)=-(α*(g:ℝ)) by ring,Real.exp_neg,←div_eq_mul_inv]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity : 0<α^(q+1)*(g:ℝ)^q)).2
  nlinarith
end WP.Analysis
