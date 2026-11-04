import Mathlib
/-! A finite compact cover combines local geometric coefficient bounds into one pair of constants, with all coefficient orders sharing the same cover. The coefficient function is fixed throughout the construction. -/
noncomputable section
namespace WP.Analysis
open Set
lemma compact_geometric_coefficient_patching {α : Type*} [TopologicalSpace α]
    (K : Set α) (hK : IsCompact K) (F : α → ℕ → ℝ) (v : ℕ → ℝ)
    (hv : ∀ n, 0 ≤ v n)
    (hlocal : ∀ x ∈ K, ∃ (U : Set α) (C B : ℝ), IsOpen U ∧ x ∈ U ∧
      0 < C ∧ 0 < B ∧ ∀ y ∈ K ∩ U, ∀ n : ℕ, F y n ≤ C * B^n * v n) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ y ∈ K, ∀ n : ℕ, F y n ≤ C * B^n * v n := by
  classical
  choose U C B hU hx hC hB he using fun x : K => hlocal x x.property
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : K => U x) hU (by
    intro x hxK
    exact mem_iUnion.mpr ⟨⟨x,hxK⟩,hx ⟨x,hxK⟩⟩)
  let C0 : ℝ := 1 + ∑ x ∈ t, C x
  let B0 : ℝ := 1 + ∑ x ∈ t, B x
  have hC0 : 0 < C0 := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun x hx => (hC x).le))
  have hB0 : 0 < B0 := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun x hx => (hB x).le))
  refine ⟨C0,B0,hC0,hB0,?_⟩
  intro y hy n
  obtain ⟨x,hxt,hyU⟩ := mem_iUnion₂.mp (ht hy)
  have hCle : C x ≤ C0 := by
    have hh := Finset.single_le_sum (f := C) (fun x hx => (hC x).le) hxt
    change C x ≤ 1 + ∑ x ∈ t, C x
    linarith only [hh]
  have hBle : B x ≤ B0 := by
    have hh := Finset.single_le_sum (f := B) (fun x hx => (hB x).le) hxt
    change B x ≤ 1 + ∑ x ∈ t, B x
    linarith only [hh]
  exact (he x y ⟨hy,hyU⟩ n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hCle (pow_le_pow_left₀ (hB x).le hBle n) (pow_nonneg (hB x).le _) hC0.le) (hv n))
end WP.Analysis
