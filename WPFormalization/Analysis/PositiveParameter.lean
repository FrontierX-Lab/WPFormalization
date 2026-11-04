import Mathlib
/-! A finite double induction for positive logarithmic parameter recurrences. -/
noncomputable section
namespace WP.Analysis
lemma inverse_log_coeff_nonneg (t u : ℕ → PowerSeries ℝ) (q : ℕ)
    (hu0 : u 0 = 1)
    (hu : ∀ (m : ℕ), PowerSeries.C (m+1 : ℝ)*u (m+1) =
      ∑ i ∈ Finset.range (m+1), PowerSeries.C (i+1 : ℝ)*(t (i+1)*u (m-i)))
    (ht : ∀ m j, j ≤ q → 0 ≤ PowerSeries.coeff j (t (m+1))) :
    ∀ m j, j ≤ q → 0 ≤ PowerSeries.coeff j (u m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro j hj
    cases m with
    | zero =>
      rw [hu0]
      by_cases hj0 : j = 0 <;> simp [hj0]
    | succ m =>
      have h := congrArg (PowerSeries.coeff j) (hu m)
      simp only [PowerSeries.coeff_C_mul,map_sum] at h
      have hs : 0 ≤ ∑ i ∈ Finset.range (m+1), (i+1 : ℝ)*PowerSeries.coeff j (t (i+1)*u (m-i)) := by
        apply Finset.sum_nonneg
        intro i hi
        apply mul_nonneg (by positivity)
        rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_nonneg
        intro k hk
        have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        exact mul_nonneg (ht i k (hkj.trans hj)) (ih (m-i) (by omega) (j-k) (by omega))
      have hp : 0 ≤ (m+1 : ℝ)*PowerSeries.coeff j (u (m+1)) := h.symm ▸ hs
      exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < m+1)).mp hp
lemma logarithmic_parameter_coeff_nonneg (t u : ℕ → PowerSeries ℝ) (α : ℝ) (hα : 0 ≤ α)
    (ht0 : ∀ m, 0 ≤ PowerSeries.coeff 0 (t (m+1)))
    (hu0 : u 0 = 1)
    (hu : ∀ (m : ℕ), PowerSeries.C (m+1 : ℝ)*u (m+1) =
      ∑ i ∈ Finset.range (m+1), PowerSeries.C (i+1 : ℝ)*(t (i+1)*u (m-i)))
    (ht : ∀ (m : ℕ), PowerSeries.derivative (t (m+1)) =
      PowerSeries.C (2*(m+2) : ℝ)*t (m+2)+PowerSeries.C α*u (m+2)) :
    (∀ q m, 0 ≤ PowerSeries.coeff q (t (m+1))) ∧
      (∀ q m, 0 ≤ PowerSeries.coeff q (u m)) := by
  have htall : ∀ q m, 0 ≤ PowerSeries.coeff q (t (m+1)) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      cases q with
      | zero => exact ht0
      | succ q =>
        have hl : ∀ m j, j ≤ q → 0 ≤ PowerSeries.coeff j (t (m+1)) :=
          fun m j hj => ih j (by omega) m
        have hul := inverse_log_coeff_nonneg t u q hu0 hu hl
        intro m
        have h := congrArg (PowerSeries.coeff q) (ht m)
        simp only [PowerSeries.coeff_derivative,map_add,PowerSeries.coeff_C_mul] at h
        have hs : 0 ≤ (2*(m+2) : ℝ)*PowerSeries.coeff q (t (m+2))+
            α*PowerSeries.coeff q (u (m+2)) := by
          exact add_nonneg (mul_nonneg (by positivity) (ih q (by omega) (m+1)))
            (mul_nonneg hα (hul (m+2) q le_rfl))
        have hp : 0 ≤ PowerSeries.coeff (q+1) (t (m+1))*(q+1 : ℝ) := h.symm ▸ hs
        exact (mul_nonneg_iff_of_pos_right (by positivity : (0 : ℝ) < q+1)).mp hp
  refine ⟨htall,?_⟩
  intro q m
  exact inverse_log_coeff_nonneg t u q hu0 hu (fun m j hj => htall j m) m q le_rfl
end WP.Analysis
