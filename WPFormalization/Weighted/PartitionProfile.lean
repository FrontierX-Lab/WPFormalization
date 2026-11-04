import WPFormalization.Weighted.TwoColorLabels
import WPFormalization.Weighted.ActiveDimension

/-! Node-independent actual clipped-weight partition envelope in terms of the selected label count. -/
noncomputable section
namespace WP
lemma clippedWeight_partition_profile (c : ℝ) (hc : 0<c) :
    ∃ C : ℝ, 0<C ∧ ∀ g : ℕ, 2≤g → ∀ pivot : ℕ, ∀ d : List ℕ, ∀ I : Finset ℕ,
      I ⊆ Finset.range d.length → ∀ u v : ℕ,
      clippedWeight c (u::selectedNat d I)*clippedWeight c (v::selectedNat d ((Finset.range d.length)\I))/
          clippedWeight c (pivot::d) ≤
        C*((I.card : ℝ)+2)*Real.sqrt (complexity g (d.length+1))/
          Real.sqrt ((inactive d).choose (inactive (selectedNat d I))) := by
  obtain ⟨C,hC,hbound⟩ := clippedWeight_partition_binomial c hc
  refine ⟨C,hC,?_⟩
  intro g hg pivot d I hI u v
  let e₁ := selectedNat d I
  let e₂ := selectedNat d ((Finset.range d.length)\I)
  let h := complexity g (d.length+1)
  have hp : (e₁++e₂).Perm d := selectedNat_partition_perm d I
  have he₁ : e₁.length=I.card := selectedNat_length d I hI
  have helen : e₁.length+e₂.length=d.length := by simpa only [List.length_append] using hp.length_eq
  have hi₁ : (inactive e₁ : ℝ)+1≤(I.card : ℝ)+1 := by exact_mod_cast (show inactive e₁+1≤I.card+1 by have := inactive_le_length e₁; omega)
  have hi₂ : (inactive e₂ : ℝ)+1≤(h : ℝ) := by
    have hn : d.length+1≤h := by dsimp only [h]; unfold complexity; omega
    exact_mod_cast (show inactive e₂+1≤h by have := inactive_le_length e₂; omega)
  have hh : (0 : ℝ)≤h := by positivity
  have hs : (0 : ℝ)≤(I.card : ℝ)+1 := by positivity
  have hraw : ((inactive e₁ : ℝ)+1)*((inactive e₂ : ℝ)+1)≤((I.card : ℝ)+2)^2*h := by
    have he := mul_le_mul hi₁ hi₂ (by positivity : (0 : ℝ)≤(inactive e₂ : ℝ)+1) (by positivity : (0 : ℝ)≤(I.card : ℝ)+1)
    have hs' : (I.card : ℝ)+1≤((I.card : ℝ)+2)^2 := by nlinarith [show (0 : ℝ)≤I.card by positivity]
    exact he.trans (mul_le_mul_of_nonneg_right hs' hh)
  have hroot := Real.sqrt_le_sqrt hraw
  rw [Real.sqrt_mul (sq_nonneg ((I.card : ℝ)+2)),Real.sqrt_sq (by positivity : (0 : ℝ)≤(I.card : ℝ)+2)] at hroot
  have hw := hbound pivot d e₁ e₂ u v hp
  norm_num only [Nat.cast_add,Nat.cast_one] at hw
  apply hw.trans
  have he := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hC.le)
    (Real.sqrt_nonneg ((inactive d).choose (inactive e₁)))
  convert he using 1 <;> ring
end WP
