import Mathlib

/-! Exact finite complexity/genus reindexing. -/
noncomputable section
namespace WP
lemma sum_complexity_reindex {α : Type*} [DecidableEq α]
    (s : Finset α) (size : α → ℕ) (g N : ℕ) (F : ℕ → ℕ → α → ℝ)
    (hF : ∀ k i a, 0≤F k i a) :
    (∑ ia ∈ ((Finset.range (g+1)) ×ˢ s).filter (fun ia =>
        2≤2*ia.1+size ia.2 ∧ 2*(2*ia.1+size ia.2-2)≤N),
        F (2*ia.1+size ia.2-2) ia.1 ia.2) ≤
      ∑ z ∈ (Finset.range (N/2+1)).sigma (fun k =>
        ((Finset.range (k+3)) ×ˢ s).filter (fun ia => size ia.2=k+2-2*ia.1)),
        F z.1 z.2.1 z.2.2 := by
  apply Finset.sum_le_sum_of_injOn (fun ia => ⟨2*ia.1+size ia.2-2,ia⟩)
  · intro ia hia ja hja he
    exact congrArg (fun z : Σ _ : ℕ, ℕ × α => z.2) he
  · intro z hz
    obtain ⟨ia,hia,rfl⟩ := Finset.mem_image.mp hz
    have hiap := Finset.mem_product.mp (Finset.mem_filter.mp hia).1
    have hic := (Finset.mem_filter.mp hia).2
    simp only [Finset.mem_sigma,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
    refine ⟨?_,⟨?_,hiap.2⟩,?_⟩ <;> omega
  · intro ia hia
    exact le_rfl
  · intro z hz hz'
    exact hF z.1 z.2.1 z.2.2
lemma sum_complexity_reindex_nested {α : Type*} [DecidableEq α]
    (s : Finset α) (size : α → ℕ) (g N : ℕ) (F : ℕ → ℕ → α → ℝ)
    (hF : ∀ k i a, 0≤F k i a) :
    (∑ i ∈ Finset.range (g+1), ∑ a ∈ s,
      if 2≤2*i+size a ∧ 2*(2*i+size a-2)≤N then F (2*i+size a-2) i a else 0) ≤
      ∑ k ∈ Finset.range (N/2+1), ∑ i ∈ Finset.range (k+3), ∑ a ∈ s,
        if size a=k+2-2*i then F k i a else 0 := by
  have he := sum_complexity_reindex s size g N F hF
  simpa only [Finset.sum_filter,Finset.sum_product,Finset.sum_sigma] using he
end WP
