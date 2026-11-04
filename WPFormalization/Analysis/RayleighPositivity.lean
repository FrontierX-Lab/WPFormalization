import Mathlib

/-! Positive Rayleigh coefficients from a normalized Bessel differential equation.
This is a purely algebraic proof over real formal power series. -/
noncomputable section
namespace WP.Analysis
open PowerSeries
lemma coeff_pos_of_riccati (p : PowerSeries ℝ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (he : C α*p+C β*(X*derivative p) = 1+C β*(X*p^2)) :
    ∀ n, 0 < coeff n p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have h := congrArg (coeff 0) he
      simp only [map_add,coeff_C_mul,coeff_zero_X_mul,mul_zero,add_zero,coeff_one,ite_true] at h
      nlinarith
    | succ n =>
      have h := congrArg (coeff (n+1)) he
      simp only [map_add,coeff_C_mul,coeff_succ_X_mul,coeff_derivative,coeff_one,
        Nat.add_eq_zero,one_ne_zero,and_false,ite_false,zero_add,pow_two] at h
      rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
      have hsum : 0 < ∑ i ∈ Finset.range (n+1), coeff i p*coeff (n-i) p := by
        apply Finset.sum_pos
        · intro i hi
          exact mul_pos (ih i (Finset.mem_range.mp hi)) (ih (n-i) (by omega))
        · exact ⟨0,by simp⟩
      have hd : 0 < α+β*(n+1 : ℝ) := by positivity
      have hm : 0 < (α+β*(n+1 : ℝ))*coeff (n+1) p := by
        nlinarith [mul_pos hβ hsum]
      exact (mul_pos_iff_of_pos_left hd).mp hm
lemma logSlope_riccati (f : PowerSeries ℝ) (α β : ℝ)
    (hf : constantCoeff f = 1)
    (he : C β*(X*derivative (derivative f))+C α*derivative f+f = 0) :
    let p := -derivative f*f⁻¹
    C α*p+C β*(X*derivative p) = 1+C β*(X*p^2) := by
  dsimp only
  let p := -derivative f*f⁻¹
  change C α*p+C β*(X*derivative p) = 1+C β*(X*p^2)
  have hf0 : constantCoeff f ≠ 0 := by rw [hf]; exact one_ne_zero
  have hfn : f ≠ 0 := by intro h; simpa [h] using hf
  have hp : p*f = -derivative f := by
    dsimp only [p]
    rw [mul_assoc,PowerSeries.inv_mul_cancel f hf0,mul_one]
  have hd : derivative p*f+p*derivative f = -derivative (derivative f) := by
    have h := congrArg derivative hp
    simpa only [Derivation.leibniz,map_neg,smul_eq_mul,mul_comm,add_comm] using h
  apply mul_right_cancel₀ hfn
  linear_combination C β*X*hd+(C α-C β*X*p)*hp-he
lemma coeff_pos_of_derivative_mul (p g : PowerSeries ℝ)
    (hp : ∀ n, 0 < coeff n p) (hg : constantCoeff g = 1)
    (he : derivative g = p*g) : ∀ n, 0 < coeff n g := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff,hg] using (zero_lt_one : (0 : ℝ)<1)
    | succ n =>
      have h := congrArg (coeff n) he
      rw [coeff_derivative,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
      have hsum : 0 < ∑ i ∈ Finset.range (n+1), coeff i p*coeff (n-i) g := by
        apply Finset.sum_pos
        · intro i hi
          exact mul_pos (hp i) (ih (n-i) (by omega))
        · exact ⟨0,by simp⟩
      have hn : (0 : ℝ)<n+1 := by positivity
      exact (mul_pos_iff_of_pos_right hn).mp (h.symm ▸ hsum)
lemma coeff_inv_pos_of_bessel_ode (f : PowerSeries ℝ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hf : constantCoeff f = 1)
    (he : C β*(X*derivative (derivative f))+C α*derivative f+f = 0) :
    ∀ n, 0 < coeff n f⁻¹ := by
  let p := -derivative f*f⁻¹
  have hp := coeff_pos_of_riccati p α β hα hβ (logSlope_riccati f α β hf he)
  apply coeff_pos_of_derivative_mul p f⁻¹ hp
  · rw [constantCoeff_inv,hf,inv_one]
  · dsimp only [p]
    rw [derivative_inv']
    ring

def normalizedBesselCoeff (α β : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => -normalizedBesselCoeff α β n/((n+1 : ℝ)*(β*n+α))
def normalizedBesselSeries (α β : ℝ) : PowerSeries ℝ := PowerSeries.mk (normalizedBesselCoeff α β)
lemma normalizedBessel_constant (α β : ℝ) : constantCoeff (normalizedBesselSeries α β) = 1 := by
  simp [normalizedBesselSeries,normalizedBesselCoeff,← coeff_zero_eq_constantCoeff]
lemma coeff_euler (f : PowerSeries ℝ) (n : ℕ) :
    coeff n (X*derivative f) = (n : ℝ)*coeff n f := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [coeff_succ_X_mul,coeff_derivative,Nat.cast_add,Nat.cast_one]
    ring
lemma normalizedBessel_ode (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    let f := normalizedBesselSeries α β
    C β*(X*derivative (derivative f))+C α*derivative f+f = 0 := by
  dsimp only
  ext n
  simp only [map_add,coeff_C_mul,coeff_euler,coeff_derivative,normalizedBesselSeries,
    coeff_mk,map_zero,normalizedBesselCoeff]
  have hd : (n+1 : ℝ)*(β*n+α) ≠ 0 := by positivity
  field_simp
  <;> ring
lemma normalizedBessel_inv_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    0 < coeff n (normalizedBesselSeries α β)⁻¹ :=
  coeff_inv_pos_of_bessel_ode _ α β hα hβ (normalizedBessel_constant α β)
    (normalizedBessel_ode α β hα hβ) n
lemma normalizedBessel_logSlope_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    0 < coeff n (-derivative (normalizedBesselSeries α β)*(normalizedBesselSeries α β)⁻¹) :=
  coeff_pos_of_riccati _ α β hα hβ (logSlope_riccati _ α β
    (normalizedBessel_constant α β) (normalizedBessel_ode α β hα hβ)) n


end WP.Analysis
