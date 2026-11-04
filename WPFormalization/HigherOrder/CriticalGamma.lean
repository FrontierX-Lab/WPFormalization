import WPFormalization.HigherOrder.SecondProfile

/-! Exact cancellation of the finite first transport coefficient at criticality.
Only the explicitly defined critical kernels and finite polynomial arithmetic
are used; no endpoint asymptotic or uniform moment estimate is assumed.
-/
noncomputable section
namespace WP.HigherOrder

@[simp] lemma weight_critical (l : ℕ) : weight y₀ l = if l = 0 then 1 else 0 := by
  by_cases h : l = 0 <;> simp [weight, critical_kernels.2,h]

@[simp] lemma A_critical : A y₀ = 2/15 := by norm_num [A,barH]
@[simp] lemma Theta_critical : Theta y₀ = 1 := by simp [Theta,weight_critical]
@[simp] lemma moment₁_critical : moment₁ y₀ = 0 := by simp [moment₁,weight_critical]
@[simp] lemma kernelMoment_critical (j : ℕ) : kernelMoment j y₀ = if j = 0 then 1 else 0 := by
  simp [kernelMoment,weight_critical,zero_pow_eq]

@[simp] lemma transportBeta_critical (p : ℕ) : transportBeta p y₀ = -(p : ℝ)/5 := by
  simp only [transportBeta,A_critical,Theta_critical,moment₁_critical]
  ring
@[simp] lemma alpha_critical (p : ℕ) : alpha p y₀ = 2*((p : ℝ)-2)/5 := by
  simp only [alpha,A_critical,Theta_critical,moment₁_critical]
  ring

lemma eulerPlusOne_affine (c : ℂ) :
    eulerPlusOne (fun z : ℂ => 1-c*z) = fun z => 1-(2*c)*z := by
  funext z
  unfold eulerPlusOne
  have hd : deriv (fun z : ℂ => 1-c*z) z = -c := by
    simpa using (((hasDerivAt_id z).const_mul c).const_sub 1).deriv
  rw [hd]
  ring

lemma critical_euler_iterate (j : ℕ) :
    (eulerPlusOne^[j]) (barH y₀) = fun z : ℂ => 1-((2 : ℂ)^j*(3/5))*z := by
  induction j with
  | zero => funext z; simp [barH]
  | succ j ih =>
      rw [Function.iterate_succ_apply',ih,eulerPlusOne_affine]
      funext z
      rw [pow_succ]
      ring

@[simp] lemma bMoment_critical (j : ℕ) :
    bMoment j y₀ = (1-(3/5 : ℝ)*2^j)/3 := by
  rw [bMoment,critical_euler_iterate]
  simp only [mul_one]
  have he : (1-(2 : ℂ)^j*(3/5 : ℂ)) = ((1-(3/5 : ℝ)*2^j : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he,Complex.ofReal_re]

set_option maxHeartbeats 1500000 in
lemma sigmaB_critical_succ (p : ℕ) :
    sigmaB (p+1) y₀ =
      (-2*(p : ℝ)^2-82*p-76-4*(Nat.choose p 2 : ℝ))/3375 := by
  norm_num [sigmaB,cubicIncrement,A_critical,Theta_critical,moment₁_critical,
    kernelMoment_critical,transportBeta_critical,alpha_critical,bMoment_critical,
    Nat.add_sub_cancel,critical_kernels.2,Polynomial.coeff_one,Polynomial.coeff_X,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ,sub_sq,pow_succ]
  <;> ring

lemma exceptionalIncrement_critical_zero (p : ℕ) :
    exceptionalIncrement (p+1) 0 y₀ =
      (-14*(p : ℝ)^2+38*p-16-4*(Nat.choose p 2 : ℝ))/225 := by
  norm_num [exceptionalIncrement,rInfinity,sInfinity,A_critical,Theta_critical,
    moment₁_critical,transportBeta_critical,alpha_critical,weight_critical,
    critical_kernels.2,Finset.sum_range_succ]
  <;> ring

lemma exceptionalIncrement_critical_one (p : ℕ) :
    exceptionalIncrement (p+1) 1 y₀ =
      (-4*(p : ℝ)^2+28*p-36-4*(Nat.choose p 2 : ℝ))/225 := by
  norm_num [exceptionalIncrement,rInfinity,sInfinity,A_critical,Theta_critical,
    moment₁_critical,transportBeta_critical,alpha_critical,weight_critical,
    critical_kernels.2,Finset.sum_range_succ]
  <;> ring

/-- The genuine finite gamma_p of Eq.C.11 vanishes at the critical endpoint. -/
theorem transportGamma_critical (p : ℕ) : transportGamma p y₀ = 0 := by
  rw [transportGamma,sigmaB_critical_succ,exceptionalIncrement_critical_zero,
    exceptionalIncrement_critical_one]
  simp only [transportBeta_critical,A_critical,critical_kernels.2]
  ring

end WP.HigherOrder
