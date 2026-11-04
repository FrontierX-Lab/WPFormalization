import WPFormalization.HigherOrder.ComplexCuspMajorant
/-! A true normalized unit-series inverse is bounded by (2-gamma)^(-1),
proved from the finite inverse coefficient recursion. No analytic convergence
or inverse-majorant property is assumed. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

def inverseUnitMajorant (g : WP.HigherOrder.Series) : WP.HigherOrder.Series := (2-g)⁻¹

lemma inverseUnitMajorant_recursion (g : WP.HigherOrder.Series)
    (hg0 : PowerSeries.constantCoeff g=1) (n : ℕ) :
    PowerSeries.coeff n (inverseUnitMajorant g)=if n=0 then 1 else
      ∑i∈Finset.HasAntidiagonal.antidiagonal n,if i.2<n then
        PowerSeries.coeff i.1 g*PowerSeries.coeff i.2 (inverseUnitMajorant g) else 0 := by
  have hc : PowerSeries.constantCoeff (2-g)=1 := by
    change PowerSeries.constantCoeff (PowerSeries.C (2:ℝ)-g)=1
    simp only [map_sub,PowerSeries.constantCoeff_C,hg0]
    norm_num
  rw [inverseUnitMajorant,PowerSeries.coeff_inv,hc]
  by_cases hn : n=0
  · simp only [ite_eq_left hn,inv_one]
  · simp only [ite_eq_right hn,inv_one,neg_one_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
    by_cases hlt : i.2<n
    · simp only [ite_eq_left hlt]
      have hi0 : i.1≠0 := by omega
      have he : PowerSeries.coeff i.1 (2-g)=-PowerSeries.coeff i.1 g := by
        change PowerSeries.coeff i.1 (PowerSeries.C (2:ℝ)-g)=-PowerSeries.coeff i.1 g
        simp only [map_sub,PowerSeries.coeff_C,ite_eq_right hi0,zero_sub]
      rw [he]
      ring
    · simp only [ite_eq_right hlt,neg_zero]

lemma inverseUnitMajorant_nonneg (g : WP.HigherOrder.Series)
    (hg0 : PowerSeries.constantCoeff g=1) (hg : ∀n,0≤PowerSeries.coeff n g) :
    ∀n,0≤PowerSeries.coeff n (inverseUnitMajorant g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [inverseUnitMajorant_recursion g hg0]
    split_ifs with hn
    · exact zero_le_one
    · apply Finset.sum_nonneg
      intro i hi
      split_ifs with hlt
      · exact mul_nonneg (hg i.1) (ih i.2 hlt)
      · exact le_rfl

lemma scaled_coeff_unit_inverse_bound (f : Series) (g : WP.HigherOrder.Series)
    (S : ℝ) (hS : 0≤S) (hf0 : PowerSeries.constantCoeff f=1)
    (hg0 : PowerSeries.constantCoeff g=1) (hg : ∀n,0≤PowerSeries.coeff n g) (N : ℕ)
    (hf : ∀i:ℕ,i≤N → ‖PowerSeries.coeff i f‖≤S^(2*i)*PowerSeries.coeff i g) :
    ‖PowerSeries.coeff N (f⁻¹)‖≤S^(2*N)*PowerSeries.coeff N (inverseUnitMajorant g) := by
  have hG0 : PowerSeries.constantCoeff (inverseUnitMajorant g)=1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff,ite_true] using inverseUnitMajorant_recursion g hg0 0
  have hmain : ∀n:ℕ,n≤N → ‖PowerSeries.coeff n (f⁻¹)‖≤S^(2*n)*PowerSeries.coeff n (inverseUnitMajorant g) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnN
      by_cases hn : n=0
      · subst n
        simp only [PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv,hf0,inv_one,
          norm_one,mul_zero,pow_zero,one_mul,hG0,le_rfl]
      · rw [PowerSeries.coeff_inv,hf0,inverseUnitMajorant_recursion g hg0,ite_eq_right hn]
        simp only [ite_eq_right hn,inv_one,neg_one_mul,norm_neg]
        rw [Finset.mul_sum]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
        by_cases hlt : i.2<n
        · simp only [ite_eq_left hlt]
          calc
            _ ≤ ‖PowerSeries.coeff i.1 f‖*‖PowerSeries.coeff i.2 (f⁻¹)‖ := norm_mul_le _ _
            _ ≤ (S^(2*i.1)*PowerSeries.coeff i.1 g)*(S^(2*i.2)*PowerSeries.coeff i.2 (inverseUnitMajorant g)) :=
              mul_le_mul (hf i.1 (by omega)) (ih i.2 hlt (by omega)) (norm_nonneg _)
                (mul_nonneg (pow_nonneg hS _) (hg i.1))
            _ = S^(2*n)*(PowerSeries.coeff i.1 g*PowerSeries.coeff i.2 (inverseUnitMajorant g)) := by
              have hp : S^(2*i.1)*S^(2*i.2)=S^(2*n) := by rw [←pow_add];congr 1;omega
              calc
                _ = (S^(2*i.1)*S^(2*i.2))*(PowerSeries.coeff i.1 g*PowerSeries.coeff i.2 (inverseUnitMajorant g)) := by ring
                _ = _ := by rw [hp]
        · simp only [ite_eq_right hlt,norm_zero,mul_zero]
          exact le_rfl
  exact hmain N le_rfl

end WP.HigherOrder.ComplexCanonical
