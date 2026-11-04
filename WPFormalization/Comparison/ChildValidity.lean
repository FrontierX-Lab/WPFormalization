import WPFormalization.Comparison.TypedStates
/-! Validity, residual degree, and exact complexity drop for the actual linear
merger and handle children. Signed invalid mergers are kept outside this
lemma and receive zero transition weight in the typed transition module. -/
noncomputable section

namespace WP
lemma mergerProfile_valid_rank (g p : ℕ) (d : List ℕ) (l j : ℕ)
    (hg : 2 ≤ g) (hd : (p::d).sum ≤ dimension g (d.length+1))
    (hl : l ≤ deficit g (p::d)) (hj : j < d.length) (hn : 1 ≤ p+d[j]!+l) :
    1 ≤ (mergerProfile p d l j).length ∧
    Stable g (mergerProfile p d l j).length ∧
    (mergerProfile p d l j).sum ≤ dimension g (mergerProfile p d l j).length ∧
    deficit g (mergerProfile p d l j) = deficit g (p::d)-l ∧
    complexity g (mergerProfile p d l j).length+1=complexity g (d.length+1) := by
  have hlen : (mergerProfile p d l j).length = d.length := by
    simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hj]
    omega
  have hsum0 : d[j]!+(d.eraseIdx j).sum=d.sum := by
    simpa [hj] using (List.getElem_cons_eraseIdx_perm hj).sum_eq
  have hsum : (mergerProfile p d l j).sum+1=(p::d).sum+l := by
    simp only [mergerProfile,List.sum_cons]
    omega
  have hdef : deficit g (p::d) = dimension g (d.length+1)-(p::d).sum := rfl
  have hadm : (mergerProfile p d l j).sum ≤ dimension g (mergerProfile p d l j).length := by
    rw [hlen]
    unfold dimension at hd ⊢
    simp only [hdef] at hl
    unfold dimension at hl
    omega
  refine ⟨by simp [mergerProfile],?_,hadm,?_,?_⟩
  · rw [hlen]
    unfold Stable
    omega
  · unfold deficit
    rw [hlen]
    unfold dimension at *
    simp only [List.length_cons] at *
    omega
  · rw [hlen]
    unfold complexity
    omega

lemma contractionProfile_valid_rank (g p : ℕ) (d : List ℕ) (l u : ℕ)
    (hg : 2 ≤ g) (hd : (p::d).sum ≤ dimension g (d.length+1))
    (hl : l ≤ deficit g (p::d)) (hu : u < p+l-1) :
    1 ≤ (contractionProfile p d l u).length ∧
    Stable (g-1) (contractionProfile p d l u).length ∧
    (contractionProfile p d l u).sum ≤ dimension (g-1) (contractionProfile p d l u).length ∧
    deficit (g-1) (contractionProfile p d l u) = deficit g (p::d)-l ∧
    complexity (g-1) (contractionProfile p d l u).length+1=complexity g (d.length+1) := by
  have hlen : (contractionProfile p d l u).length = d.length+2 := by simp [contractionProfile]
  have hsum : (contractionProfile p d l u).sum+2=(p::d).sum+l := by
    simp only [contractionProfile,List.sum_cons]
    omega
  have hdef : deficit g (p::d) = dimension g (d.length+1)-(p::d).sum := rfl
  have hadm : (contractionProfile p d l u).sum ≤ dimension (g-1) (contractionProfile p d l u).length := by
    rw [hlen]
    unfold dimension at hd ⊢
    simp only [hdef] at hl
    unfold dimension at hl
    omega
  refine ⟨by simp [contractionProfile],?_,hadm,?_,?_⟩
  · rw [hlen]
    unfold Stable
    omega
  · unfold deficit
    rw [hlen]
    unfold dimension at *
    simp only [List.length_cons] at *
    omega
  · rw [hlen]
    unfold complexity
    omega
end WP
