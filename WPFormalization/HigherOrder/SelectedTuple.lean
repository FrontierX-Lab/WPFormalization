import WPFormalization.HigherOrder.MergerTuple
/-! The actual selectedNat list is exactly a finite coordinate projection in its original label order. Its subset and complement have the proved cardinalities. The distinguished pivot mask is identified with the actual first degree; no label permutation is assumed. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary

def selectedIndices (n : ℕ) (I : Finset ℕ) : List ℕ :=
  (List.range n).filter (fun k => k ∈ I)

lemma selectedIndices_mem_lt {n k : ℕ} {I : Finset ℕ} (hk : k ∈ selectedIndices n I) : k < n := by
  exact List.mem_range.mp (List.mem_filter.mp hk).1

lemma selectedIndices_nodup (n : ℕ) (I : Finset ℕ) : (selectedIndices n I).Nodup :=
  (List.nodup_range (n := n)).filter _

lemma selectedIndices_toFinset (n : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range n) :
    (selectedIndices n I).toFinset = I := by
  ext k
  simp only [List.mem_toFinset, selectedIndices, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hk
    exact ⟨Finset.mem_range.mp (hI hk), hk⟩

lemma selectedIndices_length (n : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range n) :
    (selectedIndices n I).length = I.card := by
  rw [← List.toFinset_card_of_nodup (selectedIndices_nodup n I), selectedIndices_toFinset n I hI]

def selectedProjection (n : ℕ) (I : Finset ℕ) : Fin (selectedIndices n I).length → Fin (n + 1) :=
  fun j => (⟨(selectedIndices n I).get j, selectedIndices_mem_lt (List.get_mem _ _)⟩ : Fin n).succ

lemma selectedNat_ofFn_projection (n : ℕ) (I : Finset ℕ) (d : Fin (n + 1) → ℕ) :
    List.ofFn (fun j => d (selectedProjection n I j)) =
      selectedNat (List.ofFn (fun i : Fin n => d i.succ)) I := by
  let f : ℕ → ℕ := fun k => (List.ofFn (fun i : Fin n => d i.succ))[k]!
  have hm := congrArg (List.map f) (List.ofFn_get (selectedIndices n I))
  rw [List.map_ofFn] at hm
  calc
    _ = List.ofFn (fun j => f ((selectedIndices n I).get j)) := by
      congr 1
      funext j
      have hj : (selectedIndices n I).get j < n := selectedIndices_mem_lt (List.get_mem _ _)
      simp only [f, List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hj, Option.getD_some]
      rfl
    _ = (selectedIndices n I).map f := hm
    _ = _ := by simp only [selectedNat, List.length_ofFn]; rfl

def selectedSubsetProjection (n : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range n) :
    Fin I.card → Fin (n + 1) :=
  fun j => selectedProjection n I (Fin.cast (selectedIndices_length n I hI).symm j)

lemma selectedNat_ofFn_subset_projection (n : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range n)
    (d : Fin (n + 1) → ℕ) :
    List.ofFn (fun j : Fin I.card => d (selectedSubsetProjection n I hI j)) =
      selectedNat (List.ofFn (fun i : Fin n => d i.succ)) I := by
  have hh := List.ofFn_congr (selectedIndices_length n I hI)
    (fun j => d (selectedProjection n I j))
  rw [selectedNat_ofFn_projection n I d] at hh
  exact hh.symm

lemma selection_complement_card (n : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range n) :
    I.card + ((Finset.range n) \ I).card = n := by
  rw [Finset.card_sdiff_of_subset hI, Finset.card_range]
  have hc : I.card ≤ n := by simpa using Finset.card_le_card hI
  omega
end WP.HigherOrder.JointBoundary

namespace WP.HigherOrder.JointBoundary

def pivotHeadCoefficients (p : ℕ) : Fin (p + 1) → ℕ := Fin.cases 1 (fun _ => 0)

lemma pivotHeadCoefficients_sum (p : ℕ) (d : Fin (p + 1) → ℕ) :
    (∑ i : Fin (p + 1), pivotHeadCoefficients p i * d i) = d 0 := by
  rw [Fin.sum_univ_succ]
  simp [pivotHeadCoefficients]
end WP.HigherOrder.JointBoundary
