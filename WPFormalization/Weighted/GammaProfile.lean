import WPFormalization.Weighted.PartitionProfile
import WPFormalization.Weighted.GammaEnvelope
import WPFormalization.Weighted.NodeConvolution

/-! Actual clipped weights and Gamma splitting normalized to the small-component label envelope. -/
noncomputable section
namespace WP
lemma gamma_clippedWeight_partition_bound (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∀ g pivot : ℕ, ∀ d : List ℕ, 2≤g → ∀ g₁ : ℕ, g₁≤g →
      ∀ I : Finset ℕ, I ⊆ Finset.range d.length →
      let e₁ := selectedNat d I
      let e₂ := selectedNat d ((Finset.range d.length)\I)
      let h₁ := complexity g₁ (e₁.length+1)
      let h₂ := complexity (g-g₁) (e₂.length+1)
      let h := complexity g (d.length+1)
      let k := h₁-1
      Stable g₁ (e₁.length+1) → Stable (g-g₁) (e₂.length+1) → h₁≤h₂ → ∀ u v : ℕ,
      (Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h)*
        (clippedWeight c (u::e₁)*clippedWeight c (v::e₂)/clippedWeight c (pivot::d))*
          Real.exp ((1/12 : ℝ)*min h₁ h₂) ≤
      C*Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2))*
        (((I.card : ℝ)+2)/((h-3).choose k : ℝ)*Real.exp ((k+1 : ℕ)/12)/
          Real.sqrt ((inactive d).choose (inactive e₁))) := by
  obtain ⟨C,hC,hbound⟩ := clippedWeight_partition_profile c hc
  refine ⟨C,hC,?_⟩
  intro g pivot d hg g₁ hg₁ I hI
  dsimp only
  intro hs₁ hs₂ hsmall u v
  let e₁ := selectedNat d I
  let e₂ := selectedNat d ((Finset.range d.length)\I)
  let h₁ := complexity g₁ (e₁.length+1)
  let h₂ := complexity (g-g₁) (e₂.length+1)
  let h := complexity g (d.length+1)
  let k := h₁-1
  change Stable g₁ (e₁.length+1) at hs₁
  change Stable (g-g₁) (e₂.length+1) at hs₂
  change h₁≤h₂ at hsmall
  have hp : (e₁++e₂).Perm d := selectedNat_partition_perm d I
  have hlen : (e₁++e₂).length=d.length := hp.length_eq
  have hsum : h₁+h₂+1=h := by
    have he := separating_complexity_add g₁ (g-g₁) e₁ e₂ hs₁ hs₂
    rw [show g₁+(g-g₁)=g by omega,hlen] at he
    exact he
  have hh₁ : 1≤h₁ := by dsimp only [h₁]; unfold Stable at hs₁; unfold complexity; omega
  have hh₂ : 1≤h₂ := by dsimp only [h₂]; unfold Stable at hs₂; unfold complexity; omega
  have hh : 3≤h := by omega
  have hk : k+1=h₁ := by dsimp only [k]; omega
  have hh₁R : (0 : ℝ)<h₁ := by exact_mod_cast (show 0<h₁ by omega)
  have hh₂R : (0 : ℝ)<h₂ := by exact_mod_cast (show 0<h₂ by omega)
  have hhR : (0 : ℝ)<h := by exact_mod_cast (show 0<h by omega)
  have hG : 0≤Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h :=
    div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos hh₁R).le (Real.Gamma_pos_of_pos hh₂R).le)
      (Real.Gamma_pos_of_pos hhR).le
  have hw := hbound g hg pivot d I hI u v
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hG)
    (Real.exp_pos ((1/12 : ℝ)*min h₁ h₂)).le
  change (Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h)*
      (clippedWeight c (u::e₁)*clippedWeight c (v::e₂)/clippedWeight c (pivot::d))*
      Real.exp ((1/12 : ℝ)*min h₁ h₂) ≤ _
  apply he.trans_eq
  have hExp : Real.exp ((1/12 : ℝ)*min h₁ h₂)=Real.exp ((k+1 : ℕ)/12) := by
    rw [Nat.min_eq_left hsmall,← hk]
    congr 1
    ring
  rw [hExp,gamma_split_binomial_complexity h h₁ h₂ hh₁ hh₂ hsum]
  change (1/(((h : ℝ)-1)*((h : ℝ)-2)*((h-3).choose k : ℝ)))*
      (C*((I.card : ℝ)+2)*Real.sqrt h/Real.sqrt ((inactive d).choose (inactive e₁)))*
      Real.exp ((k+1 : ℕ)/12) =
      C*Real.sqrt h/(((h : ℝ)-1)*((h : ℝ)-2))*
        (((I.card : ℝ)+2)/((h-3).choose k : ℝ)*Real.exp ((k+1 : ℕ)/12)/
          Real.sqrt ((inactive d).choose (inactive e₁)))
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
end WP
