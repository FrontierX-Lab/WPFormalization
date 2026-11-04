import WPFormalization.External.SpecialFunctions
/-! Actual positive Gamma falling ratios, with a truncation-uniform bound used in endpoint matching. -/
noncomputable section
namespace WP.Analysis
lemma gamma_falling_ratio_product (ν : ℝ) (L : ℕ) (hx : 0 < ν-(L:ℝ)) :
    Real.Gamma (ν-(L:ℝ))/Real.Gamma ν=
      ∏ j ∈ Finset.range L, (ν-(L:ℝ)+(j:ℝ))⁻¹ := by
  have hn : (ν-(L:ℝ))+(L:ℝ)=ν := by ring
  have hprod := External.gamma_finite_product (ν-(L:ℝ)) hx L
  rw [hn] at hprod
  rw [hprod]
  have hG : Real.Gamma (ν-(L:ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  rw [Finset.prod_inv_distrib]
  field_simp
lemma gamma_falling_ratio_bound (ν a : ℝ) (L : ℕ) (ha : 0 < a)
    (hlower : a ≤ ν-(L:ℝ)) :
    0 < Real.Gamma (ν-(L:ℝ))/Real.Gamma ν ∧
      Real.Gamma (ν-(L:ℝ))/Real.Gamma ν ≤ a⁻¹^L := by
  have hx : 0 < ν-(L:ℝ) := ha.trans_le hlower
  have hν : 0 < ν := by linarith [Nat.cast_nonneg (α:=ℝ) L]
  refine ⟨div_pos (Real.Gamma_pos_of_pos hx) (Real.Gamma_pos_of_pos hν),?_⟩
  rw [gamma_falling_ratio_product ν L hx]
  calc
    _ ≤ ∏ j ∈ Finset.range L, a⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro j hj
        positivity
      · intro j hj
        apply inv_anti₀ ha
        linarith [Nat.cast_nonneg (α:=ℝ) j]
    _ = _ := by simp
lemma gamma_painleve_falling_ratio_bound (g L : ℕ) (hg : 1 ≤ g) (hL : 2*L ≤ g) :
    Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ))/Real.Gamma (2*(g:ℝ)-1/2) ≤ (g:ℝ)⁻¹^L := by
  have hg0 : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  apply (gamma_falling_ratio_bound (2*(g:ℝ)-1/2) (g:ℝ) L hg0 _).2
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hLr : 2*(L:ℝ) ≤ g := by exact_mod_cast hL
  linarith
end WP.Analysis
