import WPFormalization.HigherOrder.JointBoundaryHead
/-! Finite parent strata determine a genuine affine child head status. For B≥b+c, the valid/invalid and low/high cases of sum a_i*d_i+l-c depend only on the parent cutoff pattern. Nonnegative integer coefficients and all finite boundary cases are retained. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary

def representative (p B : ℕ) (σ : Fin p → Option (Fin (B + 1))) : Fin p → ℕ :=
  fun i => (σ i).elim (B + 1) Fin.val

lemma representative_classify_low {p : ℕ} (B : ℕ) (d : Fin p → ℕ)
    (i : Fin p) (hi : d i ≤ B) :
    representative p B (classify p B d) i = d i := by
  simp only [representative, classify, dite_eq_left hi, Option.elim_some]

lemma representative_classify_high {p : ℕ} (B : ℕ) (d : Fin p → ℕ)
    (i : Fin p) (hi : B < d i) :
    representative p B (classify p B d) i = B + 1 := by
  simp only [representative, classify, dite_eq_right (not_le.mpr hi), Option.elim_none]

lemma classify_representative {p : ℕ} (b B : ℕ) (hb : b ≤ B) (d : Fin p → ℕ) :
    classify p b (representative p B (classify p B d)) = classify p b d := by
  funext i
  by_cases hi : d i ≤ B
  · change (if h : representative p B (classify p B d) i ≤ b then
      some (⟨representative p B (classify p B d) i, by omega⟩ : Fin (b + 1)) else none) =
      (if h : d i ≤ b then some (⟨d i, by omega⟩ : Fin (b + 1)) else none)
    simp only [representative_classify_low B d i hi]
  · have hbig := representative_classify_high B d i (by omega)
    change (if h : representative p B (classify p B d) i ≤ b then
      some (⟨representative p B (classify p B d) i, by omega⟩ : Fin (b + 1)) else none) =
      (if h : d i ≤ b then some (⟨d i, by omega⟩ : Fin (b + 1)) else none)
    simp only [hbig, dite_eq_right (by omega : ¬B + 1 ≤ b), dite_eq_right (by omega : ¬d i ≤ b)]

def affineHeadStatus (b c s l : ℕ) : Option (Option (Fin (b + 1))) :=
  if c ≤ s + l then
    some (if h : s + l - c ≤ b then some ⟨s + l - c, by omega⟩ else none)
  else none

lemma affineHeadStatus_large (b c s l : ℕ) (hs : b + c < s) :
    affineHeadStatus b c s l = some none := by
  simp only [affineHeadStatus, ite_eq_left (by omega : c ≤ s + l),
    dite_eq_right (by omega : ¬s + l - c ≤ b)]

lemma affineHeadStatus_eq_representative {p : ℕ} (b c B l : ℕ) (hB : b + c ≤ B)
    (a d : Fin p → ℕ) :
    affineHeadStatus b c (∑ i : Fin p, a i * d i) l =
      affineHeadStatus b c (∑ i : Fin p, a i * representative p B (classify p B d) i) l := by
  by_cases hh : ∃ i : Fin p, a i ≠ 0 ∧ B < d i
  · obtain ⟨i, hai, hdi⟩ := hh
    have hd : d i ≤ ∑ k : Fin p, a k * d k := by
      have had : d i ≤ a i * d i := by
        simpa using Nat.mul_le_mul_right (d i) (show 1 ≤ a i by omega)
      exact had.trans (Finset.single_le_sum (f := fun k : Fin p => a k * d k)
        (fun k hk => Nat.zero_le _) (Finset.mem_univ i))
    have hr : B + 1 ≤ ∑ k : Fin p, a k * representative p B (classify p B d) k := by
      have hrep := representative_classify_high B d i hdi
      calc
        B + 1 = representative p B (classify p B d) i := hrep.symm
        _ ≤ a i * representative p B (classify p B d) i := by
          simpa using Nat.mul_le_mul_right (representative p B (classify p B d) i)
            (show 1 ≤ a i by omega)
        _ ≤ _ := Finset.single_le_sum
          (f := fun k : Fin p => a k * representative p B (classify p B d) k)
          (fun k hk => Nat.zero_le _) (Finset.mem_univ i)
    rw [affineHeadStatus_large b c _ l (by omega), affineHeadStatus_large b c _ l (by omega)]
  · have he : (∑ i : Fin p, a i * d i) =
        ∑ i : Fin p, a i * representative p B (classify p B d) i := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hai : a i = 0
      · simp only [hai, zero_mul]
      · have hdi : d i ≤ B := by
          by_contra hn
          exact hh ⟨i, hai, by omega⟩
        rw [representative_classify_low B d i hdi]
    rw [he]
end WP.HigherOrder.JointBoundary
