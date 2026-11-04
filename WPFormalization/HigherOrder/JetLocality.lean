import WPFormalization.HigherOrder.FiniteSeries

/-! Exact coefficient locality of the actual finite formal operations:
products, inverses, complexity substitution, coefficientwise sums, and
finite sums/products. A zero constant prefactor saves one coefficient. -/
set_option autoImplicit false
noncomputable section
namespace WP.HigherOrder
open PowerSeries
/-- Agreement of all coefficients strictly below the displayed cutoff. -/
def AgreeBelow (N : ℕ) (f g : Series) : Prop := ∀ k < N,PowerSeries.coeff k f = PowerSeries.coeff k g
lemma AgreeBelow.refl (N : ℕ) (f : Series) : AgreeBelow N f f := fun _ _ => rfl
lemma AgreeBelow.symm {N : ℕ} {f g : Series} (h : AgreeBelow N f g) : AgreeBelow N g f :=
  fun k hk => (h k hk).symm
lemma AgreeBelow.mono {M N : ℕ} {f g : Series} (h : AgreeBelow N f g) (hMN : M ≤ N) : AgreeBelow M f g :=
  fun k hk => h k (lt_of_lt_of_le hk hMN)
lemma AgreeBelow.add {N : ℕ} {f g a b : Series} (hf : AgreeBelow N f g) (ha : AgreeBelow N a b) :
    AgreeBelow N (f+a) (g+b) := by
  intro k hk
  simp only [map_add,hf k hk,ha k hk]
lemma AgreeBelow.mul {N : ℕ} {f g a b : Series} (hf : AgreeBelow N f g) (ha : AgreeBelow N a b) :
    AgreeBelow N (f*a) (g*b) := by
  intro k hk
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hf ij.1 (by omega),ha ij.2 (by omega)]
lemma AgreeBelow.inv {N : ℕ} {f g : Series} (hf : AgreeBelow N f g) :
    AgreeBelow N f⁻¹ g⁻¹ := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hc : constantCoeff f = constantCoeff g := by
      simpa only [← coeff_zero_eq_constantCoeff] using hf 0 (by omega)
    rw [PowerSeries.coeff_inv,PowerSeries.coeff_inv,hc]
    by_cases hk0 : k = 0
    · simp only [hk0,ite_true]
    · simp only [hk0,ite_false]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hj : ij.2 < k
      · simp only [hj,ite_true]
        rw [hf ij.1 (by omega),ih ij.2 hj (by omega)]
      · simp only [hj,ite_false]
lemma AgreeBelow.shift {N : ℕ} {f g : Series} (hf : AgreeBelow N f g) (c : ℝ) :
    AgreeBelow N (WP.HigherOrder.complexityShift c f) (WP.HigherOrder.complexityShift c g) := by
  intro k hk
  unfold WP.HigherOrder.complexityShift
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (shiftVariable_constant c)),
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (shiftVariable_constant c))]
  apply finsum_congr
  intro j
  by_cases hj : j < N
  · rw [hf j hj]
  · have hkj : ¬ j ≤ k := by omega
    have hz : PowerSeries.coeff k (shiftVariable c^j) = 0 := by
      rw [shiftVariable,mul_pow,PowerSeries.coeff_X_pow_mul',if_neg hkj]
    simp only [hz,smul_zero]
lemma AgreeBelow.coefficientSum {N : ℕ} {f g : ℕ → Series}
    (h : ∀ l,AgreeBelow N (f l) (g l)) : AgreeBelow N (WP.HigherOrder.coefficientSum f) (WP.HigherOrder.coefficientSum g) := by
  intro k hk
  simp only [coefficientSum_coeff]
  apply tsum_congr
  intro l
  exact h l k hk
lemma AgreeBelow.sum {α : Type*} {N : ℕ} (s : Finset α) (f g : α → Series)
    (h : ∀ i ∈ s,AgreeBelow N (f i) (g i)) :
    AgreeBelow N (∑ i ∈ s,f i) (∑ i ∈ s,g i) := by
  intro k hk
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact h i hi k hk
lemma AgreeBelow.prod {α : Type*} [DecidableEq α] {N : ℕ} (s : Finset α) (f g : α → Series)
    (h : ∀ i ∈ s,AgreeBelow N (f i) (g i)) :
    AgreeBelow N (∏ i ∈ s,f i) (∏ i ∈ s,g i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using AgreeBelow.refl N (1:Series)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
lemma coeff_mul_eq_of_zero_constant {K : ℕ} {f g u : Series}
    (hu : constantCoeff u = 0) (h : AgreeBelow K f g) :
    PowerSeries.coeff K (u*f) = PowerSeries.coeff K (u*g) := by
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hz : ij.1 = 0
  · rw [hz,coeff_zero_eq_constantCoeff,hu,zero_mul,zero_mul]
  · rw [h ij.2 (by omega)]

end WP.HigherOrder
