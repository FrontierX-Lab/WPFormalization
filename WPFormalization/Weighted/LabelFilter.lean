import WPFormalization.Weighted.TwoColorLabels
import WPFormalization.Weighted.LabelEntropy

/-! Exact filtered label-spectrum counting, retaining the genus-zero inactive support condition. -/
noncomputable section
namespace WP
lemma card_two_color_split {α : Type*} [DecidableEq α] (A B U : Finset α)
    (hAB : Disjoint A B) (hU : U ⊆ A∪B) : U.card=(U∩A).card+(U∩B).card := by
  have he : (U∩A)∪(U∩B)=U := by
    ext x
    simp only [Finset.mem_union,Finset.mem_inter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases Finset.mem_union.mp (hU h) with hA | hB
      · exact Or.inl ⟨h,hA⟩
      · exact Or.inr ⟨h,hB⟩
  have hd : Disjoint (U∩A) (U∩B) := hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hc := Finset.card_union_of_disjoint hd
  rw [he] at hc
  exact hc
lemma powerset_filtered_label_envelope {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (s : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (∑ U ∈ (A∪B).powerset, if U.card=s ∧ q (U∩A).card then
      1/Real.sqrt (A.card.choose (U∩A).card) else 0) =
      ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal s, if q uv.1 then
        Real.sqrt (A.card.choose uv.1)*(B.card.choose uv.2 : ℝ) else 0 := by
  calc
    _ = ∑ U ∈ (A∪B).powerset, if (U∩A).card+(U∩B).card=s ∧ q (U∩A).card then
        1/Real.sqrt (A.card.choose (U∩A).card) else 0 := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [card_two_color_split A B U hAB (Finset.mem_powerset.mp hU)]
    _ = ∑ u ∈ Finset.range (A.card+1), ∑ v ∈ Finset.range (B.card+1),
        (A.card.choose u : ℝ)*(B.card.choose v : ℝ)*
          (if u+v=s ∧ q u then 1/Real.sqrt (A.card.choose u) else 0) :=
      sum_powerset_two_colors_choose A B hAB (fun u v => if u+v=s ∧ q u then 1/Real.sqrt (A.card.choose u) else 0)
    _ = ∑ u ∈ Finset.range (A.card+1), ∑ v ∈ Finset.range (B.card+1),
        if u+v=s then (if q u then Real.sqrt (A.card.choose u) else 0)*(B.card.choose v : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      by_cases he : u+v=s <;> by_cases hq : q u <;> simp only [he,hq,ite_true,ite_false,true_and,false_and,mul_zero,zero_mul]
      rw [show (A.card.choose u : ℝ)*(B.card.choose v : ℝ)*(1/Real.sqrt (A.card.choose u)) =
          ((A.card.choose u : ℝ)/Real.sqrt (A.card.choose u))*(B.card.choose v : ℝ) by ring,Real.div_sqrt]
    _ = ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal s,
        (if q uv.1 then Real.sqrt (A.card.choose uv.1) else 0)*(B.card.choose uv.2 : ℝ) :=
      binomial_grid_antidiagonal A.card B.card s
        (fun u => if q u then Real.sqrt (A.card.choose u) else 0) (fun v => (B.card.choose v : ℝ))
        (by intro u hu; split_ifs <;> simp [Nat.choose_eq_zero_of_lt hu])
        (by intro v hv; simp [Nat.choose_eq_zero_of_lt hv])
    _ = _ := by
      apply Finset.sum_congr rfl
      intro uv huv
      split_ifs <;> ring
end WP
