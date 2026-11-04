import WPFormalization.Statements.Basic

/-! Local Taylor coefficient congruence, real scaling, and inverse powers.
All lemmas below have Lean proofs and no paper-specific hypotheses. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology

lemma iteratedDeriv_comp_mul_left (f : ℂ → ℂ) (c : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => f (c*w)) z = c^n*iteratedDeriv n f (c*z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun w => f (c*w)) = fun w => c^n*iteratedDeriv n f (c*w) :=
      funext ih
    rw [he,deriv_const_mul_field,deriv_comp_mul_left,iteratedDeriv_succ,pow_succ]
    ring
lemma coeff_congr_of_eventuallyEq (f g : ℂ → ℂ) (h : f =ᶠ[𝓝 0] g) (n : ℕ) : coeff f n = coeff g n := by
  unfold coeff
  rw [h.iteratedDeriv_eq n]
lemma realCoeff_const_mul (f : ℂ → ℂ) (c : ℝ) (n : ℕ) :
    realCoeff (fun w => (c : ℂ)*f w) n = c*realCoeff f n := by
  unfold realCoeff coeff
  rw [iteratedDeriv_const_mul_field]
  rw [mul_div_assoc,Complex.mul_re]
  simp
lemma realCoeff_comp_mul_left (f : ℂ → ℂ) (c : ℝ) (n : ℕ) :
    realCoeff (fun w => f ((c : ℂ)*w)) n = c^n*realCoeff f n := by
  unfold realCoeff coeff
  rw [iteratedDeriv_comp_mul_left,mul_zero,mul_div_assoc]
  have hc : (c : ℂ)^n = Complex.ofReal (c^n) := by norm_cast
  rw [hc,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
lemma inverseLinear_coeff_pos (h n : ℕ) (hh : 0 < h) :
    0 < realCoeff (fun z : ℂ => (1-z)⁻¹^h) n := by
  have he : (fun z : ℂ => (1-z)⁻¹^h) = fun z => (1-z)^(-(h : ℤ)) := by
    funext z
    simp
  unfold realCoeff coeff
  rw [he]
  have heq : (fun z : ℂ => (1-z)^(-(h : ℤ))) =
      (fun z : ℂ => (fun w : ℂ => w^(-(h : ℤ))) (1-z)) := rfl
  rw [heq,iteratedDeriv_comp_const_sub (f := fun w : ℂ => w^(-(h : ℤ))) (s := (1 : ℂ))]
  simp only [iteratedDeriv_eq_iterate,iter_deriv_zpow',Int.cast_neg,Int.cast_natCast,
    sub_zero,one_zpow,mul_one,smul_eq_mul]
  have hp : (∏ i ∈ Finset.range n, (-(h : ℂ)-(i : ℂ))) =
      (-1 : ℂ)^n * ∏ i ∈ Finset.range n, ((h : ℂ)+i) := by
    calc
      _ = ∏ i ∈ Finset.range n, -((h : ℂ)+i) :=
        Finset.prod_congr rfl (fun i hi => by ring)
      _ = _ := by rw [Finset.prod_neg]; simp only [Finset.card_range]
  rw [hp]
  have hn : (-1 : ℂ)^n*((-1 : ℂ)^n * ∏ i ∈ Finset.range n, ((h : ℂ)+i)) =
      ∏ i ∈ Finset.range n, ((h : ℂ)+i) := by
    rw [← mul_assoc,← mul_pow]
    simp
  rw [hn]
  have hc : (∏ i ∈ Finset.range n, ((h : ℂ)+i)) / (n.factorial : ℂ) =
      Complex.ofReal ((∏ i ∈ Finset.range n, ((h : ℝ)+i))/(n.factorial : ℝ)) := by
    push_cast
    <;> rfl
  rw [hc,Complex.ofReal_re]
  apply div_pos
  · apply Finset.prod_pos
    intro i hi
    exact add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hh) (Nat.cast_nonneg i)
  · exact_mod_cast Nat.factorial_pos n

lemma realCoeff_inv_pow_eq_exp (f : ℂ → ℂ) (hf : ContinuousAt f 0) (hf0 : f 0 ≠ 0)
    (h n : ℕ) : realCoeff (fun z => (f z)⁻¹^h) n =
      realCoeff (fun z => Complex.exp (-(h : ℂ)*Complex.log (f z))) n := by
  have he : (fun z => (f z)⁻¹^h) =ᶠ[𝓝 0]
      (fun z => Complex.exp (-(h : ℂ)*Complex.log (f z))) := by
    filter_upwards [hf.eventually_ne hf0] with z hz
    simp only [neg_mul,Complex.exp_neg,Complex.exp_nat_mul,Complex.exp_log hz,inv_pow]
  exact congrArg Complex.re (coeff_congr_of_eventuallyEq _ _ he n)

end WP.Analysis
