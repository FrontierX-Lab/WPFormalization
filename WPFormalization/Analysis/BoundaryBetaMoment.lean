import WPFormalization.Statements.Basic

/-! Exact beta moments for the original bounded-boundary Bessel integral. The proof is polynomial differentiation and the fundamental theorem of calculus; it does not use a deferred special-function result. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory

def boundaryBetaMoment (b : ℕ) : ℝ := ∫ s : ℝ in (0)..1, (1-s^2)^b

lemma boundaryBetaMoment_recurrence (b : ℕ) :
    (2*(b:ℝ)+3)*boundaryBetaMoment (b+1) = (2*(b:ℝ)+2)*boundaryBetaMoment b := by
  let F : ℝ → ℝ := fun s => s*(1-s^2)^(b+1)
  let f : ℝ → ℝ := fun s => (2*(b:ℝ)+3)*(1-s^2)^(b+1) - (2*(b:ℝ)+2)*(1-s^2)^b
  have hd : ∀ s : ℝ, HasDerivAt F (f s) s := by
    intro s
    have hp := (((hasDerivAt_const s (1:ℝ)).sub ((hasDerivAt_id s).pow 2)).pow (b+1))
    have h := (hasDerivAt_id s).mul hp
    convert h using 1
    · rfl
    · dsimp [f]
      simp only [Nat.cast_add,Nat.cast_one,pow_one]
      rw [pow_succ]
      ring
  have hi : (∫ s in (0:ℝ)..1, f s) = 0 := by
    have hc : Continuous f := by dsimp [f];fun_prop
    simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hd s) (hc.intervalIntegrable 0 1)
  have h0 : IntervalIntegrable (fun s : ℝ => (1-s^2)^b) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h1 : IntervalIntegrable (fun s : ℝ => (1-s^2)^(b+1)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  dsimp [f] at hi
  rw [intervalIntegral.integral_sub (h1.const_mul _) (h0.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hi
  exact sub_eq_zero.mp hi

lemma boundaryBetaMoment_value (b : ℕ) :
    boundaryBetaMoment b = (2:ℝ)^b * (b.factorial:ℝ)/(WP.oddFactorial b:ℝ) := by
  induction b with
  | zero => norm_num [boundaryBetaMoment,WP.oddFactorial]
  | succ b ih =>
    have hr := boundaryBetaMoment_recurrence b
    rw [ih] at hr
    have ho : WP.oddFactorial (b+1) = WP.oddFactorial b*(2*(b+1)+1) := by
      simp only [WP.oddFactorial,Finset.prod_range_succ]
    rw [ho,Nat.cast_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    have hz : (WP.oddFactorial b:ℝ) ≠ 0 := by
      have hp : 0 < WP.oddFactorial b := Finset.prod_pos (fun i _ => by omega)
      exact_mod_cast hp.ne'
    have hc : (2:ℝ)*(b+1)+1 ≠ 0 := by positivity
    push_cast
    field_simp [hz,hc] at hr ⊢
    nlinarith only [hr]
end WP.Analysis
