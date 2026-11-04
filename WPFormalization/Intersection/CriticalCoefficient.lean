import WPFormalization.Intersection.Finite

/-! Explicit coefficients of the critical linear kernel and endpoint normalization. -/
noncomputable section
namespace WP

lemma deriv_affine_zpow (c : ℂ) (k : ℤ) (z : ℂ) :
    deriv (fun w : ℂ => (1-c*w)^k) z =
      -c*(k : ℂ)*(1-c*z)^(k-1) := by
  have h := deriv_comp_mul_left c (fun w : ℂ => (1-w)^k) z
  rw [deriv_comp_const_sub (fun w : ℂ => w^k) 1 (c*z), deriv_zpow] at h
  simpa only [Function.comp_def, smul_eq_mul, mul_neg, neg_mul, mul_assoc] using h

lemma iteratedDeriv_affine_inv_pow (c : ℂ) (h n : ℕ) :
    iteratedDeriv n (fun z : ℂ => (1-c*z)⁻¹^h) =
      fun z => (h.ascFactorial n : ℂ)*c^n*(1-c*z)^(-((h+n : ℕ) : ℤ)) := by
  induction n with
  | zero =>
      funext z
      simp [zpow_neg, inv_pow]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      rw [deriv_const_mul_field]
      rw [deriv_affine_zpow]
      have he : -((h+n : ℕ) : ℤ)-1 = -((h+(n+1) : ℕ) : ℤ) := by omega
      rw [he]
      simp only [Nat.ascFactorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Int.cast_neg, pow_succ]
      push_cast
      ring

lemma harmonicCoeff_critical (h m : ℕ) :
    harmonicCoeff y₀ h m = (h.ascFactorial m : ℝ)*(3/5 : ℝ)^m/m.factorial := by
  unfold harmonicCoeff realCoeff coeff
  have hb : barH y₀ = fun z : ℂ => 1-3/5*z := by funext z; simp [barH]
  rw [hb, iteratedDeriv_affine_inv_pow]
  simp only [mul_zero, sub_zero, one_zpow, mul_one]
  have he : ((h.ascFactorial m : ℂ)*(3/5 : ℂ)^m/(m.factorial : ℂ)) =
      (((h.ascFactorial m : ℝ)*(3/5 : ℝ)^m/(m.factorial : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.ofReal_re]

lemma gamma_mul_ascFactorial (h m : ℕ) (hh : 1 ≤ h) :
    Real.Gamma h * (h.ascFactorial m : ℝ) = Real.Gamma (h+m : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hn : (h+m : ℕ) ≠ 0 := by omega
      have hnr : ((h+m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn
      simp only [Nat.ascFactorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hpos : 0 < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
      rw [show (h : ℝ)+((m : ℝ)+1) = ((h : ℝ)+m)+1 by ring,
        Real.Gamma_add_one (by positivity : (h : ℝ)+m ≠ 0)]
      simp only [Nat.cast_add] at ih
      rw [← ih]
      ring

lemma model_critical (g : ℕ) (d : List ℕ) (hh : 1 ≤ complexity g d.length) :
    model g d y₀ =
      (3 : ℝ)^(complexity g d.length+deficit g d) *
        Real.Gamma (complexity g d.length+deficit g d : ℕ) /
        (4^g*5^(deficit g d)*(deficit g d).factorial) := by
  unfold model
  rw [harmonicCoeff_critical]
  rw [← gamma_mul_ascFactorial _ _ hh, pow_add, div_pow]
  field_simp

lemma endpoint_normalization (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    ratio P g (List.replicate p 0) y₀ =
      pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2) := by
  have hst : Stable g p := by unfold Stable; omega
  have hh : 1 ≤ complexity g p := by unfold complexity; omega
  have hc : complexity g (p+dimension g p) = complexity g p+dimension g p := by
    unfold complexity
    omega
  have hm : deficit g (List.replicate p 0) = dimension g p := by simp [deficit]
  have hn : normalized P g (List.replicate p 0) y₀ =
      (3 : ℝ)^(dimension g p) *
        P.psi g (List.replicate p 0 ++ List.replicate (dimension g p) 2) /
        (dimension g p).factorial := by
    simp [normalized, hst, deficit, pure, oddFactorial]
  unfold ratio
  rw [hn, model_critical g (List.replicate p 0) (by simpa using hh),
    pureC_zeros_twos_formula]
  simp only [List.length_replicate, hm, hc, pow_add]
  have hG : Real.Gamma (complexity g p+dimension g p : ℕ) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by exact_mod_cast (by omega : 0 < complexity g p+dimension g p)))
  have hp : (dimension g p).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [show (15 : ℝ) = 3*5 by norm_num, mul_pow]
  field_simp

end WP
