import WPFormalization.Weighted.TransitionWeights

/-! Actual active-label counts forced by the degree-dimension constraint. -/
noncomputable section
namespace WP
lemma inactive_le_length (d : List ℕ) : inactive d ≤ d.length := by
  unfold inactive
  exact List.length_filter_le _ _
lemma active_twice_le_sum (d : List ℕ) : 2*(d.length-inactive d) ≤ d.sum := by
  induction d with
  | nil => simp [inactive]
  | cons k d ih =>
    have hi := inactive_le_length d
    simp only [List.length_cons,inactive_cons_eq,List.sum_cons]
    by_cases hk : k ≤ 1
    · simp only [hk,ite_true]
      omega
    · simp only [hk,ite_false,zero_add]
      omega
lemma active_dimension_bound (g : ℕ) (d : List ℕ) (hg : 2 ≤ g)
    (hd : d.sum ≤ dimension g d.length) :
    4*(d.length-inactive d)+d.length ≤ 3*complexity g d.length ∧
      5*(d.length-inactive d) ≤ 3*complexity g d.length := by
  have ha := active_twice_le_sum d
  have hi := inactive_le_length d
  unfold dimension complexity at *
  omega
lemma active_tail_dimension_bound (g pivot : ℕ) (d : List ℕ) (hg : 2 ≤ g)
    (hd : (pivot::d).sum ≤ dimension g (d.length+1))
    (hh : 30 ≤ complexity g (d.length+1)) :
    inactive d+(d.length-inactive d) ≤ complexity g (d.length+1)-3 ∧
      3*(d.length-inactive d) ≤ 2*(complexity g (d.length+1)-3) := by
  have hi := inactive_le_length d
  have ha := active_dimension_bound g (pivot::d) hg (by simpa only [List.length_cons] using hd)
  have hp : d.length-inactive d ≤ (pivot::d).length-inactive (pivot::d) := by
    rw [List.length_cons,inactive_cons_eq]
    split_ifs <;> omega
  have hn : d.length ≤ complexity g (d.length+1)-3 := by unfold complexity; omega
  simp only [List.length_cons] at ha hp
  constructor
  · omega
  · omega
lemma genus_zero_inactive_surplus (node : ℕ) (d : List ℕ)
    (hd : node+d.sum ≤ dimension 0 (d.length+1)) (hs : Stable 0 (d.length+1)) :
    d.length-inactive d+2 ≤ inactive d := by
  have ha := active_twice_le_sum d
  have hi := inactive_le_length d
  unfold Stable at hs
  unfold dimension at hd
  omega
end WP
