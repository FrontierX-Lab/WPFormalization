import WPFormalization.HigherOrder.PoissonFiniteOrders
import WPFormalization.Analysis.QuadraticRemainder
noncomputable section
namespace WP.HigherOrder
open scoped Topology
lemma poisson_shifted_coeff_norm (R M : ℝ) (hR : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hb : ∀z∈Metric.closedBall (0:ℂ) R,‖f z‖ ≤ M) (ν : ℂ) (hν : ‖ν‖ ≤ R/4) (m : ℕ) :
    ‖WP.coeff (fun z=>f (ν+z)) m‖ ≤ M/(R/2)^m := by
  have hball (z : ℂ) (hz : z∈Metric.closedBall (0:ℂ) (R/2)) :
      ν+z∈Metric.closedBall (0:ℂ) R := by
    have hz' : ‖z‖ ≤ R/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have ht := norm_add_le ν z
    linarith
  apply Analysis.coeff_norm_le_circle_bound _ (R/2) M (half_pos hR) _ _ m
  · intro z hz
    exact ((hf _ (hball z hz)).differentiableAt.comp z (by fun_prop)).differentiableWithinAt
  · intro z hz
    exact hb _ (hball z (Metric.sphere_subset_closedBall hz))

lemma poisson_factorial_ratio_half (j m : ℕ) (hjm : j ≤ m) (hm : m ≤ 2*j) :
    (m.factorial:ℝ)/((m-j).factorial:ℝ) ≤ (4:ℝ)^j*(j.factorial:ℝ) := by
  have he : (m.factorial:ℝ)/((m-j).factorial:ℝ)=(m.descFactorial j:ℝ) := by
    apply (div_eq_iff (by positivity : ((m-j).factorial:ℝ)≠0)).mpr
    have ht : ((m-j).factorial:ℝ)*(m.descFactorial j:ℝ)=(m.factorial:ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hjm
    nlinarith
  rw [he]
  have ht:=Analysis.descFactorial_half_order_le j m j hm le_rfl
  simpa only [Nat.sub_self,pow_zero,mul_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    (show (m.descFactorial j:ℝ) ≤ ((4^j*j.factorial*j^(j-j):ℕ):ℝ) by exact_mod_cast ht)

lemma poissonCentralFunctional_norm_le (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (c : ℕ → ℂ) (hc : ∀m,‖c m‖ ≤ M/r^m) (ν : ℂ) (hν : ‖ν‖ ≤ 1) (j : ℕ) :
    ‖poissonCentralFunctional c j ν‖ ≤ M*(8*(max 1 (2/r))^2)^j*(j.factorial:ℝ) := by
  by_cases hj : j=0
  · subst j
    simpa only [poissonCentralFunctional,ite_true,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,div_one] using hc 0
  have hjp : 1 ≤ j := by omega
  let B : ℝ := max 1 (2/r)
  let E : ℝ := M*(4*B^2)^j*(j.factorial:ℝ)
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hterm (m : ℕ) (hm : m∈Finset.Icc (j+1) (2*j)) :
      ‖((poissonCentralPolynomial m).coeff (m-j):ℂ)*ν^(m-j)*c m‖ ≤ E := by
    have hm' := Finset.mem_Icc.mp hm
    have hcoef := poissonCentralPolynomial_coeff_abs m (m-j)
    have hfac := poisson_factorial_ratio_half j m (by omega) hm'.2
    have hp : (2/r)^m ≤ B^(2*j) :=
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hm'.2)
    have hv : ‖ν‖^(m-j) ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg ν) hν (m-j)
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    calc _ ≤ ((2:ℝ)^m*(m.factorial:ℝ)/((m-j).factorial:ℝ))*1*(M/r^m) :=
            mul_le_mul (mul_le_mul hcoef hv (by positivity) (by positivity)) (hc m) (by positivity) (by positivity)
         _ = M*(2/r)^m*((m.factorial:ℝ)/((m-j).factorial:ℝ)) := by rw [div_pow];ring
         _ ≤ M*B^(2*j)*((4:ℝ)^j*(j.factorial:ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hp hM) hfac (by positivity) (by positivity)
         _ = _ := by dsimp [E];rw [pow_mul,mul_pow];ring
  rw [poissonCentralFunctional,ite_eq_right hj]
  calc _ ≤ ∑m∈Finset.Icc (j+1) (2*j),‖((poissonCentralPolynomial m).coeff (m-j):ℂ)*ν^(m-j)*c m‖ := norm_sum_le _ _
       _ ≤ ∑m∈Finset.Icc (j+1) (2*j),E := Finset.sum_le_sum hterm
       _ = (j:ℝ)*E := by
          simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]
          rw [show 2*j+1-(j+1)=j by omega]
       _ ≤ (2:ℝ)^j*E := mul_le_mul_of_nonneg_right (by exact_mod_cast (j.lt_two_pow_self).le) hE
       _ = _ := by
          have hp : (8*(max 1 (2/r))^2)^j=(2:ℝ)^j*(4*(max 1 (2/r))^2)^j := by rw [←mul_pow];congr 1;ring
          rw [hp]
          dsimp [E,B]
          ring
end WP.HigherOrder
