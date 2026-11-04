import WPFormalization.Weighted.LinearNormalization
import WPFormalization.Weighted.TransitionWeights

/-! Actual finite label savings and contraction-birth budgets for the clipped state weight. -/
noncomputable section
namespace WP
lemma inactive_index_sum (d : List ℕ) :
    (∑ j ∈ Finset.range d.length, if d[j]! ≤ 1 then (1 : ℕ) else 0) = inactive d := by
  induction d with
  | nil => simp [inactive]
  | cons k d ih =>
    simp only [List.length_cons,Finset.sum_range_succ',List.getElem!_cons_zero,
      List.getElem!_cons_succ,ih,inactive_cons_eq]
lemma merger_savings_of_caps (c : ℝ) (pivot : ℕ) (d : List ℕ) (l : ℕ)
    (hall : ∀ j ∈ Finset.range d.length,
      stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) ≤ 1)
    (hinactive : ∀ j ∈ Finset.range d.length, d[j]! ≤ 1 →
      stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) ≤ inactiveMergeRatio c (inactive (pivot :: d))) :
    (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j)) ≤
      (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))-
        (1-inactiveMergeRatio c (inactive (pivot :: d)))*inactive d := by
  have he := finite_label_savings (Finset.range d.length)
    ((Finset.range d.length).filter (fun j => d[j]! ≤ 1)) (Finset.filter_subset _ _)
    (fun j => 2*(d[j]! : ℝ)+1)
    (fun j => stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j))
    (inactiveMergeRatio c (inactive (pivot :: d))) (inactiveMergeRatio_le_one c _)
    (by
      intro j hj
      have hn : (0 : ℝ) ≤ (d[j]! : ℝ) := Nat.cast_nonneg _
      linarith) hall
    (by intro j hj; exact hinactive j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)
  have hcard : ((Finset.range d.length).filter (fun j => d[j]! ≤ 1)).card = inactive d := by
    simpa only [Finset.sum_boole,Nat.cast_id] using inactive_index_sum d
  simpa only [hcard] using he
lemma contraction_layer_upper (c : ℝ) (hc : 0 ≤ c) (pivot : ℕ) (d : List ℕ) (l : ℕ) :
    (∑ u ∈ Finset.range (pivot+l-1), stateWeightRatio c (pivot :: d) (contractionProfile pivot d l u)) ≤
      (pivot+l-1 : ℕ)+64*(1+c*Real.sqrt (inactive (pivot :: d)+2))^2 := by
  have he := sum_contraction_weight_upper (pivot+l-1)
    (fun u => stateWeightRatio c (pivot :: d) (contractionProfile pivot d l u))
    (16*(1+c*Real.sqrt (inactive (pivot :: d)+2))^2) (by positivity)
    (by intro u hu; exact contraction_weight_birth c hc pivot u (pivot+l-2-u) d)
    (by
      intro u hu hu₂ hv₂
      apply contraction_weight_nonincrease c pivot u (pivot+l-2-u) d hu₂
      omega)
  nlinarith [he]
lemma layer_bound_of_caps (c : ℝ) (hc : 0 < c) (hsmall : c ≤ 1/64)
    (pivot : ℕ) (d : List ℕ) (l : ℕ)
    (hvalid : ∀ j ∈ Finset.range d.length, 1 ≤ pivot+d[j]!+l)
    (hall : ∀ j ∈ Finset.range d.length,
      stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) ≤ 1)
    (hinactive : ∀ j ∈ Finset.range d.length, d[j]! ≤ 1 →
      stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) ≤ inactiveMergeRatio c (inactive (pivot :: d))) :
    weightedLinearLayer c pivot d l ≤ (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+
      2*(pivot+l-1 : ℕ)+2048 := by
  have hm := merger_savings_of_caps c pivot d l hall hinactive
  have hn := contraction_layer_upper c hc.le pivot d l
  have hbudget := weighted_linear_birth_budget c hc hsmall (inactive (pivot :: d))
  have hi := (inactive_cons_bounds pivot d).2
  have hpen : (1-inactiveMergeRatio c (inactive (pivot :: d)))*(inactive (pivot :: d)-1 : ℕ) ≤
      (1-inactiveMergeRatio c (inactive (pivot :: d)))*inactive d := by
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast (show inactive (pivot :: d)-1 ≤ inactive d by omega))
    exact sub_nonneg.mpr (inactiveMergeRatio_le_one c _)
  unfold weightedLinearLayer
  have he : (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
      (if 1 ≤ pivot+d[j]!+l then stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) else 0)) =
      ∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (hvalid j hj)]
  rw [he]
  nlinarith
lemma weightedLinearLayer_positive_bound (c : ℝ) (hc : 0 < c) (hsmall : c ≤ 1/64)
    (pivot : ℕ) (hp : 1 ≤ pivot) (d : List ℕ) (l : ℕ) :
    weightedLinearLayer c pivot d l ≤ (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1))+
      2*(pivot+l-1 : ℕ)+2048 := by
  apply layer_bound_of_caps c hc hsmall pivot d l
  · intro j hj; omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    have hperm : (d[j]! :: d.eraseIdx j).Perm d := by simpa [hj'] using List.getElem_cons_eraseIdx_perm hj'
    have he := merger_weight_nonincrease c pivot d[j]! l (d.eraseIdx j) hp
    rw [clippedWeight_perm c (List.Perm.cons pivot hperm)] at he
    exact he
  · intro j hj hq
    have hj' := Finset.mem_range.mp hj
    have hperm : (d[j]! :: d.eraseIdx j).Perm d := by simpa [hj'] using List.getElem_cons_eraseIdx_perm hj'
    by_cases hp1 : pivot=1
    · subst pivot
      have he := one_pivot_merger_weight c d[j]! l (d.eraseIdx j)
      rw [clippedWeight_perm c (List.Perm.cons 1 hperm),inactive_perm (List.Perm.cons 1 hperm)] at he
      simpa only [stateWeightRatio,mergerProfile,show 1+d[j]!+l-1=d[j]!+l by omega] using he
    · have he := active_inactive_merger_weight c pivot d[j]! l (d.eraseIdx j) (by omega) hq
      rw [clippedWeight_perm c (List.Perm.cons pivot hperm),inactive_perm (List.Perm.cons pivot hperm)] at he
      exact he
lemma weightedLinearLayer_zero_bound (c : ℝ) (hc : 0 < c) (hsmall : c ≤ 1/64)
    (d : List ℕ) (hd : ∀ k ∈ d, k=0) (l : ℕ) (hl : 1 ≤ l) :
    weightedLinearLayer c 0 d l ≤ (d.length : ℝ)+2*(l-1 : ℕ)+2048 := by
  have hz : ∀ j ∈ Finset.range d.length, d[j]! = 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    apply hd
    simpa [hj'] using (List.getElem_mem (l := d) j hj')
  have hcap : ∀ j ∈ Finset.range d.length,
      stateWeightRatio c (0 :: d) (mergerProfile 0 d l j) ≤ inactiveMergeRatio c (inactive (0 :: d)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hperm : (0 :: d.eraseIdx j).Perm d := by
      have he : (d[j]! :: d.eraseIdx j).Perm d := by simpa [hj'] using List.getElem_cons_eraseIdx_perm hj'
      simpa only [hz j hj] using he
    have he := zero_pivot_merger_weight c (l-1) (d.eraseIdx j)
    rw [clippedWeight_perm c (List.Perm.cons 0 hperm),inactive_perm (List.Perm.cons 0 hperm)] at he
    simpa only [stateWeightRatio,mergerProfile,hz j hj,zero_add] using he
  have he := layer_bound_of_caps c hc hsmall 0 d l
    (by intro j hj; omega)
    (by intro j hj; exact (hcap j hj).trans (inactiveMergeRatio_le_one c _))
    (by intro j hj hq; exact hcap j hj)
  have hsum : (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)) = d.length := by
    calc
      _ = ∑ j ∈ Finset.range d.length, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        norm_num [hz j hj]
      _ = _ := by simp
  simpa only [hsum,zero_add] using he

end WP
