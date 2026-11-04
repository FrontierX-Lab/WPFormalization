import WPFormalization.Intersection.GeneralMarkedStringAll
import WPFormalization.Marked.ExternalStringFinite
noncomputable section
namespace WP
lemma external_list_ofFn_update {p : ℕ} (b : Fin p → ℕ) (i : Fin p) (k : ℕ) :
    (List.ofFn b).set i.val k = List.ofFn (Function.update b i k) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp [List.getElem_set, Function.update, Fin.ext_iff, eq_comm]
/-- The genuine unweighted shifted amplitude with a fixed external tuple and q zero insertions. -/
def externalMarkedAmplitude (P : PsiTheory) (g : ℕ) {p : ℕ} (q : ℕ) (b : Fin p → ℕ) (Y : ℝ) : ℝ :=
  shifted P g (List.replicate q 0 ++ List.ofFn b) Y /
    externalOddWeight (List.replicate q 0 ++ List.ofFn b)
lemma externalMarkedAmplitude_hasDerivAt (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g)
    {p : ℕ} (q : ℕ) (b : Fin p → ℕ) (Y : ℝ) (ha : a Y ≠ 0) :
    HasDerivAt (externalMarkedAmplitude P g q b)
      (a Y * externalMarkedAmplitude P g (q+1) b Y -
        ∑ i : Fin p, if 0 < b i then externalMarkedAmplitude P g q (Function.update b i (b i-1)) Y else 0) Y := by
  let d := List.replicate q 0 ++ List.ofFn b
  have hs : Stable g d.length := by unfold Stable;omega
  have hd := shifted_unweighted_marked_hasDerivAt_all P g d hs Y ha
  have hchild : 0::d = List.replicate (q+1) 0 ++ List.ofFn b := by
    simp [d,List.replicate_succ]
  rw [hchild] at hd
  have he : (∑ j ∈ Finset.range d.length, if 0 < d[j]! then
      shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) else 0) =
      ∑ i : Fin p, if 0 < b i then externalMarkedAmplitude P g q (Function.update b i (b i-1)) Y else 0 := by
    have hlen : d.length = q+p := by simp [d]
    rw [hlen,Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range q, if 0 < d[j]! then
      shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hget : d[j]! = 0 := by
        simp only [d,List.getElem!_eq_getElem?_getD]
        rw [List.getElem?_append_left (by simpa)]
        simp [hj']
      simp [hget]
    rw [hz,zero_add,←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hget : d[q+i.val]! = b i := by
      simp only [d,List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp)]
      simp
    rw [hget]
    split_ifs
    · have hset : d.set (q+i.val) (b i-1) = List.replicate q 0 ++ List.ofFn (Function.update b i (b i-1)) := by
        simp only [d]
        rw [List.set_append_right (q+i.val) (b i-1) (by simp)]
        simp only [List.length_replicate,Nat.add_sub_cancel_left,external_list_ofFn_update]
      simp only [hset,externalMarkedAmplitude]
    · rfl
  rw [he] at hd
  exact hd
end WP
namespace WP
lemma externalMarkedAmplitude_excess (P : PsiTheory) (g : ℕ) {p : ℕ} (q : ℕ)
    (b : Fin p → ℕ) (hd : dimension g (q+p) < ∑ i, b i) (Y : ℝ) :
    externalMarkedAmplitude P g q b Y = 0 := by
  apply shifted_unweighted_excess
  simpa only [List.length_append,List.length_replicate,List.length_ofFn,
    List.sum_append,List.sum_replicate,nsmul_zero,zero_add,List.sum_ofFn] using hd
lemma externalMarkedAmplitude_analyticAt (P : PsiTheory) (g : ℕ) {p : ℕ} (q : ℕ)
    (b : Fin p → ℕ) (Y : ℝ) (ha : a Y ≠ 0) :
    AnalyticAt ℝ (externalMarkedAmplitude P g q b) Y :=
  shifted_external_analyticAt P g _ Y ha
end WP
namespace WP
/-- Finite external boundary insertion at a fixed additional zero count. -/
def externalStringAmplitude (P : PsiTheory) (g : ℕ) {p : ℕ}
    (K : Fin p → ℕ → ℝ → ℝ) (q : ℕ) (Y : ℝ) : ℝ :=
  ∑ b ∈ externalDegreeBox p (dimension g (q+p)), externalMarkedAmplitude P g q b Y * ∏ i, K i (b i) Y

lemma externalStringAmplitude_eq_box (P : PsiTheory) (g : ℕ) {p : ℕ}
    (K : Fin p → ℕ → ℝ → ℝ) (q B : ℕ) (hB : dimension g (q+p) ≤ B) (Y : ℝ) :
    externalStringAmplitude P g K q Y =
      ∑ b ∈ externalDegreeBox p B, externalMarkedAmplitude P g q b Y * ∏ i, K i (b i) Y := by
  unfold externalStringAmplitude
  apply Finset.sum_subset
  · intro b hb
    apply (mem_externalDegreeBox p B b).mpr
    exact fun i => ((mem_externalDegreeBox p _ b).mp hb i).trans hB
  · intro b hb hnot
    have he : ∃ i, dimension g (q+p) < b i := by
      rw [mem_externalDegreeBox] at hnot
      push Not at hnot
      exact hnot
    obtain ⟨i,hi⟩ := he
    have hs : b i ≤ ∑ j, b j := Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)
    rw [externalMarkedAmplitude_excess P g q b (by omega) Y, zero_mul]

lemma externalStringAmplitude_hasDerivAt (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) {p : ℕ}
    (K : Fin p → ℕ → ℝ → ℝ) (q : ℕ) (Y : ℝ) (ha : a Y ≠ 0)
    (hK : ∀ i n, HasDerivAt (K i n) (K i (n+1) Y) Y) :
    HasDerivAt (externalStringAmplitude P g K q)
      (a Y * externalStringAmplitude P g K (q+1) Y) Y := by
  have hdim : dimension g (q+1+p) = dimension g (q+p)+1 := by
    unfold dimension
    omega
  have hf : externalStringAmplitude P g K q = fun y =>
      ∑ b ∈ externalDegreeBox p (dimension g (q+1+p)), externalMarkedAmplitude P g q b y * ∏ i, K i (b i) y :=
    funext (externalStringAmplitude_eq_box P g K q _ (by omega))
  rw [hf]
  have hd := hasDerivAt_externalDegreeBox (B:=dimension g (q+1+p)) (externalMarkedAmplitude P g) K q Y (a Y)
    (fun b _ => externalMarkedAmplitude_hasDerivAt P g hg q b Y ha) hK ?_
  · simpa only [externalStringAmplitude] using hd
  · intro b hb i hbi
    apply externalMarkedAmplitude_excess
    have hs : b i ≤ ∑ j, b j := Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)
    omega
end WP
