import WPFormalization.HigherOrder.PoissonCentralTarget
import WPFormalization.Analysis.PoissonTailFactorial
noncomputable section
namespace WP.HigherOrder
open scoped Topology
lemma poisson_retained_term_bound (h r M : ℝ) (hh : 0 < h) (hr : 0 < r)
    (hM : 0 ≤ M) (N m a : ℕ) (ha : a ≤ m) (hm : m ≤ 2*N)
    (hj : N ≤ m-a) (hN : (N:ℝ) ≤ h) (ν c : ℂ) (hν : ‖ν‖ ≤ 1)
    (hc : ‖c‖ ≤ M/r^m) :
    ‖c*((poissonCentralPolynomial m).coeff a:ℂ)*ν^a/(h:ℂ)^(m-a)‖ ≤
      M*(4*(max 1 (2/r))^2)^N*(N.factorial:ℝ)/h^N := by
  let B : ℝ := max 1 (2/r)
  have hB : 1 ≤ B := le_max_left _ _
  have h2r : 2/r ≤ B := le_max_right _ _
  have hp : (2/r)^m ≤ B^(2*N) :=
    (pow_le_pow_left₀ (by positivity) h2r _).trans (pow_le_pow_right₀ hB hm)
  have hcoef := poissonCentralPolynomial_coeff_abs m a
  have hfac := Analysis.factorial_ratio_inverse_order_le h hh N m a ha hm hj hN
  rw [norm_div,norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
  have hv : ‖ν‖^a ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg ν) hν a
  calc _ ≤ (M/r^m)*((2:ℝ)^m*(m.factorial:ℝ)/(a.factorial:ℝ))*1/h^(m-a) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul _ hv (by positivity) (by positivity)
          exact mul_le_mul hc hcoef (by positivity) (by positivity)
       _ = M*(2/r)^m*((m.factorial:ℝ)/(a.factorial:ℝ)/h^(m-a)) := by
          rw [div_pow]
          ring
       _ ≤ M*B^(2*N)*((4:ℝ)^N*(N.factorial:ℝ)/h^N) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp hM) hfac (by positivity) (by positivity)
       _ = _ := by rw [pow_mul,mul_pow];ring
lemma poisson_retained_rectangle_card (N : ℕ) (hN : 1 ≤ N) :
    (2*N)*(N+1) ≤ 4^N := by
  have htwo : 2*N ≤ 2^N := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
    induction n with
    | zero => norm_num
    | succ n ih =>
      calc 2*(n+1+1) ≤ 2*(2*(n+1)) := by omega
           _ ≤ 2*2^(n+1) := Nat.mul_le_mul_left 2 (ih (by omega))
           _ = 2^(n+1+1) := by rw [pow_succ];ring
  calc _ ≤ 2^N*2^N := Nat.mul_le_mul htwo (Nat.succ_le_of_lt (N.lt_two_pow_self))
       _ = _ := by rw [←mul_pow];norm_num

def poissonRetainedTail (h : ℝ) (ν : ℂ) (c : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑m∈Finset.range (2*N),∑a∈Finset.range (N+1),
    if a ≤ m ∧ N ≤ m-a then
      c m*((poissonCentralPolynomial m).coeff a:ℂ)*ν^a/(h:ℂ)^(m-a) else 0

lemma poissonRetainedTail_norm_le (h r M : ℝ) (hh : 0 < h) (hr : 0 < r)
    (hM : 0 ≤ M) (N : ℕ) (hN : 1 ≤ N) (hNh : (N:ℝ) ≤ h)
    (ν : ℂ) (hν : ‖ν‖ ≤ 1) (c : ℕ → ℂ) (hc : ∀m,‖c m‖ ≤ M/r^m) :
    ‖poissonRetainedTail h ν c N‖ ≤
      M*(16*(max 1 (2/r))^2)^N*(N.factorial:ℝ)/h^N := by
  let E : ℝ := M*(4*(max 1 (2/r))^2)^N*(N.factorial:ℝ)/h^N
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hterm (m a : ℕ) (hm : m∈Finset.range (2*N)) :
      ‖if a ≤ m ∧ N ≤ m-a then
        c m*((poissonCentralPolynomial m).coeff a:ℂ)*ν^a/(h:ℂ)^(m-a) else 0‖ ≤ E := by
    split_ifs with hma
    · exact poisson_retained_term_bound h r M hh hr hM N m a hma.1
        (by have ht:=Finset.mem_range.mp hm;omega) hma.2 hNh ν (c m) hν (hc m)
    · simpa using hE
  unfold poissonRetainedTail
  calc _ ≤ ∑m∈Finset.range (2*N),∑a∈Finset.range (N+1),
          ‖if a ≤ m ∧ N ≤ m-a then
            c m*((poissonCentralPolynomial m).coeff a:ℂ)*ν^a/(h:ℂ)^(m-a) else 0‖ := by
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro m hm
          exact norm_sum_le _ _
       _ ≤ ∑m∈Finset.range (2*N),∑a∈Finset.range (N+1),E := by
          apply Finset.sum_le_sum
          intro m hm
          apply Finset.sum_le_sum
          intro a ha
          exact hterm m a hm
       _ = ((2*N)*(N+1):ℕ)*E := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul];ring
       _ ≤ (4:ℝ)^N*E := mul_le_mul_of_nonneg_right (by exact_mod_cast poisson_retained_rectangle_card N hN) hE
       _ = _ := by
          have hp : (16*(max 1 (2/r))^2)^N=(4:ℝ)^N*(4*(max 1 (2/r))^2)^N := by
            rw [←mul_pow]
            congr 1
            ring
          rw [hp]
          dsimp [E]
          ring

end WP.HigherOrder
