import WPFormalization.Comparison.ChildValidity
/-! Finite typed linear transitions of the actual comparison recursion.
All terminal transitions have weight zero and use the current state as a
fallback. Invalid signed mergers likewise receive exactly zero weight.
Every nonzero nonterminal transition is an actual stable admissible child
and lowers complexity by exactly one. The final finite identity works for
any function of the actual genus and degree tuple, so mass, zero potential,
and amplitude ratios use the same transition system. -/
noncomputable section

namespace WP.ComparisonState

def linearDeficit (x : ComparisonState) : ℕ := deficit x.genus (x.pivot::x.tail)
def linearIndex (x : ComparisonState) : Type :=
  (Fin (x.linearDeficit+1) × Fin x.tail.length) ⊕
    (Σ l : Fin (x.linearDeficit+1), Fin (x.pivot+l.val-1))
noncomputable instance linearIndex_fintype (x : ComparisonState) : Fintype x.linearIndex := by
  unfold linearIndex
  infer_instance

noncomputable def linearMerger (x : ComparisonState) (hx : ¬x.terminal)
    (l : Fin (x.linearDeficit+1)) (j : Fin x.tail.length)
    (hn : 1 ≤ x.pivot+x.tail[j.val]!+l.val) : ComparisonState :=
  ⟨(x.genus,mergerProfile x.pivot x.tail l.val j.val),by
    have h := mergerProfile_valid_rank x.genus x.pivot x.tail l.val j.val
      (x.nonterminal_genus hx) x.pivot_admissible (by have := l.isLt;unfold linearDeficit at *;omega)
      j.isLt hn
    exact ⟨h.1,h.2.1,h.2.2.1⟩⟩

noncomputable def linearHandle (x : ComparisonState) (hx : ¬x.terminal)
    (l : Fin (x.linearDeficit+1)) (u : Fin (x.pivot+l.val-1)) : ComparisonState :=
  ⟨(x.genus-1,contractionProfile x.pivot x.tail l.val u.val),by
    have h := contractionProfile_valid_rank x.genus x.pivot x.tail l.val u.val
      (x.nonterminal_genus hx) x.pivot_admissible (by have := l.isLt;unfold linearDeficit at *;omega)
      u.isLt
    exact ⟨h.1,h.2.1,h.2.2.1⟩⟩

noncomputable def linearChild (x : ComparisonState) (i : x.linearIndex) : ComparisonState := by
  classical
  exact if ht : x.terminal then x else
    match i with
    | Sum.inl ij => if hn : 1 ≤ x.pivot+x.tail[ij.2.val]!+ij.1.val then
        x.linearMerger ht ij.1 ij.2 hn else x
    | Sum.inr lu => x.linearHandle ht lu.1 lu.2

def linearLayerWeight (Y : ℝ) (x : ComparisonState) (l : ℕ) : ℝ :=
  linearQ Y x.rank x.linearDeficit l / (3*((x.rank:ℝ)-1))

noncomputable def linearWeight (Y : ℝ) (x : ComparisonState) (i : x.linearIndex) : ℝ := by
  classical
  exact if x.terminal then 0 else
    match i with
    | Sum.inl ij => if 1 ≤ x.pivot+x.tail[ij.2.val]!+ij.1.val then
        x.linearLayerWeight Y ij.1.val * (2*(x.tail[ij.2.val]!:ℝ)+1) else 0
    | Sum.inr lu => x.linearLayerWeight Y lu.1.val * 2

lemma linearMerger_rank (x : ComparisonState) (hx : ¬x.terminal)
    (l : Fin (x.linearDeficit+1)) (j : Fin x.tail.length)
    (hn : 1 ≤ x.pivot+x.tail[j.val]!+l.val) : (x.linearMerger hx l j hn).rank+1=x.rank := by
  change complexity x.genus (mergerProfile x.pivot x.tail l.val j.val).length+1=x.rank
  rw [←x.rank_pivot]
  exact (mergerProfile_valid_rank x.genus x.pivot x.tail l.val j.val
    (x.nonterminal_genus hx) x.pivot_admissible (by have := l.isLt;unfold linearDeficit at *;omega)
    j.isLt hn).2.2.2.2

lemma linearHandle_rank (x : ComparisonState) (hx : ¬x.terminal)
    (l : Fin (x.linearDeficit+1)) (u : Fin (x.pivot+l.val-1)) :
    (x.linearHandle hx l u).rank+1=x.rank := by
  change complexity (x.genus-1) (contractionProfile x.pivot x.tail l.val u.val).length+1=x.rank
  rw [←x.rank_pivot]
  exact (contractionProfile_valid_rank x.genus x.pivot x.tail l.val u.val
    (x.nonterminal_genus hx) x.pivot_admissible (by have := l.isLt;unfold linearDeficit at *;omega)
    u.isLt).2.2.2.2

lemma linearChild_rank (Y : ℝ) (x : ComparisonState) (hx : ¬x.terminal)
    (i : x.linearIndex) (hi : x.linearWeight Y i ≠ 0) : (x.linearChild i).rank+1=x.rank := by
  classical
  cases i with
  | inl ij =>
    by_cases hn : 1 ≤ x.pivot+x.tail[ij.2.val]!+ij.1.val
    · simpa only [linearChild,dif_neg hx,dif_pos hn] using x.linearMerger_rank hx ij.1 ij.2 hn
    · simp only [linearWeight,if_neg hx,if_neg hn] at hi
      exact False.elim (hi rfl)
  | inr lu =>
    simpa only [linearChild,dif_neg hx] using x.linearHandle_rank hx lu.1 lu.2

lemma rank_nonterminal (x : ComparisonState) (hx : ¬x.terminal) : 2 ≤ x.rank := by
  have hg := x.nonterminal_genus hx
  have hn := x.nonempty
  unfold rank complexity
  omega

lemma linearWeight_nonneg (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (x : ComparisonState) (i : x.linearIndex) : 0 ≤ x.linearWeight Y i := by
  classical
  by_cases ht : x.terminal
  · simp [linearWeight,ht]
  · have hh := x.rank_nonterminal ht
    have hf (l : ℕ) : 0 ≤ x.linearLayerWeight Y l := by
      exact div_nonneg (linearQ_nonneg Y hY _ _ _ hh) (by
        have hr : (2:ℝ) ≤ x.rank := by exact_mod_cast hh
        nlinarith)
    cases i with
    | inl ij =>
      by_cases hn : 1 ≤ x.pivot+x.tail[ij.2.val]!+ij.1.val
      · simp only [linearWeight,if_neg ht,if_pos hn]
        exact mul_nonneg (hf _) (by positivity)
      · simp only [linearWeight,if_neg ht,if_neg hn,le_refl]
    | inr lu =>
      simp only [linearWeight,if_neg ht]
      exact mul_nonneg (hf _) (by norm_num)
end WP.ComparisonState
namespace WP.ComparisonState
lemma linear_sum_flatten_fin (Y : ℝ) (x : ComparisonState) (hx : ¬x.terminal)
    (F : ℕ → List ℕ → ℝ) :
    (∑ i : x.linearIndex, x.linearWeight Y i *
      F (x.linearChild i).genus (x.linearChild i).degrees) =
    ∑ l : Fin (x.linearDeficit+1), x.linearLayerWeight Y l.val *
      ((∑ j : Fin x.tail.length, (2*(x.tail[j.val]!:ℝ)+1)*
        (if 1 ≤ x.pivot+x.tail[j.val]!+l.val then
          F x.genus (mergerProfile x.pivot x.tail l.val j.val) else 0)) +
       2*∑ u : Fin (x.pivot+l.val-1),
         F (x.genus-1) (contractionProfile x.pivot x.tail l.val u.val)) := by
  classical
  have hm (l : Fin (x.linearDeficit+1)) (j : Fin x.tail.length) :
      x.linearWeight Y (Sum.inl (l,j)) *
        F (x.linearChild (Sum.inl (l,j))).genus (x.linearChild (Sum.inl (l,j))).degrees =
      x.linearLayerWeight Y l.val * (2*(x.tail[j.val]!:ℝ)+1)*
        (if 1 ≤ x.pivot+x.tail[j.val]!+l.val then
          F x.genus (mergerProfile x.pivot x.tail l.val j.val) else 0) := by
    by_cases hn : 1 ≤ x.pivot+x.tail[j.val]!+l.val
    · simp only [linearWeight,if_neg hx,if_pos hn,linearChild,dif_neg hx,dif_pos hn,linearMerger,genus,degrees]
    · simp only [linearWeight,if_neg hx,if_neg hn,linearChild,dif_neg hx,dif_neg hn,zero_mul,mul_zero]
  have hu (l : Fin (x.linearDeficit+1)) (u : Fin (x.pivot+l.val-1)) :
      x.linearWeight Y (Sum.inr ⟨l,u⟩) *
        F (x.linearChild (Sum.inr ⟨l,u⟩)).genus (x.linearChild (Sum.inr ⟨l,u⟩)).degrees =
      x.linearLayerWeight Y l.val * 2 *
        F (x.genus-1) (contractionProfile x.pivot x.tail l.val u.val) := by
    simp only [linearWeight,if_neg hx,linearChild,dif_neg hx,linearHandle,genus,degrees]
  calc
    _ = (∑ l : Fin (x.linearDeficit+1), ∑ j : Fin x.tail.length,
          x.linearLayerWeight Y l.val * (2*(x.tail[j.val]!:ℝ)+1)*
            (if 1 ≤ x.pivot+x.tail[j.val]!+l.val then
              F x.genus (mergerProfile x.pivot x.tail l.val j.val) else 0)) +
        ∑ l : Fin (x.linearDeficit+1), ∑ u : Fin (x.pivot+l.val-1),
          x.linearLayerWeight Y l.val * 2 *
            F (x.genus-1) (contractionProfile x.pivot x.tail l.val u.val) := by
      unfold linearIndex
      rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_sigma]
      apply congrArg₂ (fun a b : ℝ => a+b)
      · apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro j hj
        exact hm l j
      · apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro u hu'
        exact hu l u
    _ = _ := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      conv_rhs => rw [mul_add]
      apply congrArg₂ (fun a b : ℝ => a+b)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      · rw [←mul_assoc,Finset.mul_sum]

lemma linear_sum_flatten (Y : ℝ) (x : ComparisonState) (hx : ¬x.terminal)
    (F : ℕ → List ℕ → ℝ) :
    (∑ i : x.linearIndex, x.linearWeight Y i *
      F (x.linearChild i).genus (x.linearChild i).degrees) =
    ∑ l ∈ Finset.range (x.linearDeficit+1), x.linearLayerWeight Y l *
      ((∑ j ∈ Finset.range x.tail.length, (2*(x.tail[j]!:ℝ)+1)*
        (if 1 ≤ x.pivot+x.tail[j]!+l then
          F x.genus (mergerProfile x.pivot x.tail l j) else 0)) +
       2*∑ u ∈ Finset.range (x.pivot+l-1),
         F (x.genus-1) (contractionProfile x.pivot x.tail l u)) := by
  let layer (l : ℕ) : ℝ := x.linearLayerWeight Y l *
      ((∑ j ∈ Finset.range x.tail.length, (2*(x.tail[j]!:ℝ)+1)*
        (if 1 ≤ x.pivot+x.tail[j]!+l then
          F x.genus (mergerProfile x.pivot x.tail l j) else 0)) +
       2*∑ u ∈ Finset.range (x.pivot+l-1),
         F (x.genus-1) (contractionProfile x.pivot x.tail l u))
  change _ = ∑ l ∈ Finset.range (x.linearDeficit+1), layer l
  rw [←Fin.sum_univ_eq_sum_range layer]
  rw [linear_sum_flatten_fin Y x hx F]
  apply Finset.sum_congr rfl
  intro l hl
  dsimp only [layer]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (2*(x.tail[j]!:ℝ)+1)*
    (if 1 ≤ x.pivot+x.tail[j]!+l.val then F x.genus (mergerProfile x.pivot x.tail l.val j) else 0))]
  rw [Fin.sum_univ_eq_sum_range (fun u : ℕ => F (x.genus-1) (contractionProfile x.pivot x.tail l.val u))]
end WP.ComparisonState
