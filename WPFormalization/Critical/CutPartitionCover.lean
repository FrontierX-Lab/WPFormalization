import WPFormalization.Critical.CutVertexPartition
noncomputable section
namespace WP.Critical
open Finset
open scoped ENNReal Classical
instance {Q u v w : ℕ} : Finite (CutVertexPartition Q u v w) :=
  Finite.of_injective (fun R : CutVertexPartition Q u v w => R.vertices)
    (by rintro ⟨a⟩ ⟨b⟩ h; cases h; rfl)

noncomputable instance {Q u v w : ℕ} : Fintype (CutVertexPartition Q u v w) := Fintype.ofFinite _

/-- Finite covering adds only nonnegative actual counting weights. -/
lemma cut_partition_sum_cover {α β : Type*} [Fintype β] (s : Finset α)
    (B : β → α → Prop) (hB : ∀ a ∈ s, ∃ b, B b a) (f : α → ℝ≥0∞) :
    (∑ a ∈ s, f a) ≤ ∑ b : β, ∑ a ∈ s.filter (B b), f a := by
  classical
  calc
    _ ≤ ∑ a ∈ s, ∑ b : β, if B b a then f a else 0 := by
      apply sum_le_sum
      intro a ha
      obtain ⟨b,hb⟩ := hB a ha
      simpa only [if_pos hb] using
        (single_le_sum (s := univ) (f := fun b : β => if B b a then f a else 0) (fun b (_ : b ∈ (univ : Finset β)) => bot_le) (mem_univ b) :
          (if B b a then f a else 0) ≤ ∑ b : β, if B b a then f a else 0)
    _ = _ := by rw [sum_comm]; congr 1; ext b; rw [sum_filter]
end WP.Critical
namespace WP.Critical
open Finset
open scoped ENNReal Classical
lemma cut_partition_sum_cover_bound {α β : Type*} [Fintype β] (s : Finset α)
    (B : β → α → Prop) (hB : ∀ a ∈ s, ∃ b, B b a) (f : α → ℝ≥0∞)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ b : β, (∑ a ∈ s.filter (B b), f a) ≤ ENNReal.ofReal M) :
    (∑ a ∈ s, f a) ≤ ENNReal.ofReal (((Fintype.card β : ℝ)+1)*M) := by
  classical
  refine (cut_partition_sum_cover s B hB f).trans ((sum_le_sum (fun b _ => hbound b)).trans ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => hM)]
  apply ENNReal.ofReal_le_ofReal
  simp only [sum_const,card_univ,nsmul_eq_mul]
  nlinarith
end WP.Critical
