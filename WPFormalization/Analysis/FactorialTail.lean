import Mathlib
/-! A finite factorial tail estimate used for the small-genus separating
range. Below the linear cutoff g/N, the ratio of successive factorial terms
is at most one half. The finite geometric sum therefore contributes O(g⁻²),
with an explicit threshold and constant. This is finite real algebra only. -/
noncomputable section
open scoped BigOperators
namespace WP.Analysis

lemma finite_dyadic_tail_bound (a : ℕ → ℝ) (N : ℕ) (ha : 0 ≤ a 1)
    (hstep : ∀ j : ℕ, 1 ≤ j → j < N → a (j+1) ≤ a j/2) :
    (∑ j ∈ Finset.range (N+1), if 1 ≤ j then a j else 0) ≤ 2*a 1 := by
  have hterm : ∀ k : ℕ, k < N → a (k+1) ≤ a 1*(1/2:ℝ)^k := by
    intro k
    induction k with
    | zero => intro hk;simp
    | succ k ih =>
      intro hk
      calc
        _ ≤ a (k+1)/2 := hstep (k+1) (by omega) (by omega)
        _ ≤ (a 1*(1/2:ℝ)^k)/2 := div_le_div_of_nonneg_right (ih (by omega)) (by norm_num)
        _ = _ := by rw [pow_succ];ring
  rw [Finset.sum_range_succ']
  simp only [Nat.le_add_left,ite_true]
  norm_num only [show ¬1 ≤ (0:ℕ) by omega,ite_false,add_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range N, a 1*(1/2:ℝ)^k := by
      exact Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.mp hk)
    _ = a 1 * ∑ k ∈ Finset.range N, (1/2:ℝ)^k := by rw [Finset.mul_sum]
    _ ≤ 2*a 1 := by nlinarith [sum_geometric_two_le N]

lemma factorial_quadratic_step (Q : ℕ) (t : ℝ) (j : ℕ) :
    (((2*(j+1)+Q).factorial:ℝ)*t^(j+1)) =
      ((2*(j:ℝ)+Q+2)*(2*(j:ℝ)+Q+1)*t) *
        (((2*j+Q).factorial:ℝ)*t^j) := by
  have he : 2*(j+1)+Q=(2*j+Q)+2 := by omega
  rw [he,Nat.factorial_succ,Nat.factorial_succ,pow_succ]
  push_cast
  ring

lemma factorial_tail_ratio_bound (Q N g j : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hN : 0 < N) (hNK : 18*K ≤ (N:ℝ)^2) (hg : N*(Q+4) ≤ g)
    (hj : j ≤ g/N) :
    (2*(j:ℝ)+Q+2)*(2*(j:ℝ)+Q+1)*(K/(g:ℝ)^2) ≤ 1/2 := by
  have hgpos : 0 < g := by nlinarith
  have hG : 0 < (g:ℝ) := by exact_mod_cast hgpos
  have hnj : j*N ≤ g := (Nat.le_div_iff_mul_le hN).mp hj
  have hnjR : (j:ℝ)*N ≤ g := by exact_mod_cast hnj
  have hgR : (N:ℝ)*((Q:ℝ)+4) ≤ g := by exact_mod_cast hg
  have h1 : (N:ℝ)*(2*(j:ℝ)+Q+2) ≤ 3*g := by nlinarith
  have h2 : (N:ℝ)*(2*(j:ℝ)+Q+1) ≤ 3*g := by nlinarith
  have hprod := mul_le_mul h1 h2
    (show 0 ≤ (N:ℝ)*(2*(j:ℝ)+Q+1) by positivity) (show 0 ≤ 3*(g:ℝ) by positivity)
  have hA : 0 ≤ (2*(j:ℝ)+Q+2)*(2*(j:ℝ)+Q+1) := by positivity
  have hsmall := mul_le_mul_of_nonneg_right hNK hA
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hG)).2
  nlinarith [hprod,hsmall]

lemma factorial_geometric_tail_bound (Q N g : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hN : 0 < N) (hNK : 18*K ≤ (N:ℝ)^2) (hg : N*(Q+4) ≤ g) :
    (∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then
      ((2*j+Q).factorial:ℝ)*(K/(g:ℝ)^2)^j else 0) ≤
      (2*((Q+2).factorial:ℝ)*K)/(g:ℝ)^2 := by
  let a (j : ℕ) : ℝ := ((2*j+Q).factorial:ℝ)*(K/(g:ℝ)^2)^j
  have ha : ∀ j, 0 ≤ a j := by intro j;dsimp [a];positivity
  have hs : ∀ j : ℕ, 1 ≤ j → j < g/N → a (j+1) ≤ a j/2 := by
    intro j hj hjN
    change ((2*(j+1)+Q).factorial:ℝ)*(K/(g:ℝ)^2)^(j+1) ≤ a j/2
    rw [factorial_quadratic_step]
    change ((2*(j:ℝ)+Q+2)*(2*(j:ℝ)+Q+1)*(K/(g:ℝ)^2))*a j ≤ a j/2
    have hr := factorial_tail_ratio_bound Q N g j K hK hN hNK hg (by omega)
    nlinarith [mul_le_mul_of_nonneg_right hr (ha j)]
  have hb := finite_dyadic_tail_bound a (g/N) (ha 1) hs
  have he : 2*1+Q=Q+2 := by omega
  calc
    _ ≤ 2*a 1 := hb
    _ = _ := by dsimp [a];rw [he,pow_one];ring
end WP.Analysis
