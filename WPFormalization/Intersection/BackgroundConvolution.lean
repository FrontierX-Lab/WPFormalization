import WPFormalization.Intersection.BackgroundSplitting
/-! The exact finite Cauchy product for exponential background insertions.
The proof reindexes pairs of component multiplicities and proves all binomial
and factorial cancellation identities explicitly. -/
noncomputable section
namespace WP
def backgroundDegree {N : ℕ} (l : Fin N → ℕ) : ℕ := ∑ i, (i.val+1)*l i
lemma backgroundDegree_add {N : ℕ} (l j : Fin N → ℕ) :
    backgroundDegree (fun i => l i+j i) = backgroundDegree l+backgroundDegree j := by
  unfold backgroundDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
lemma backgroundDegree_sub_add {N : ℕ} (l j : Fin N → ℕ) (hj : ∀ i, j i ≤ l i) :
    backgroundDegree j+backgroundDegree (fun i => l i-j i) = backgroundDegree l := by
  unfold backgroundDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.mul_add, Nat.add_sub_of_le (hj i)]
lemma sum_background_decompose {N B m : ℕ} (hm : m ≤ B)
    (F : (Fin N → ℕ) → (Fin N → ℕ) → ℝ) :
    (∑ l ∈ backgroundVectors N B m, ∑ j ∈ subBackgrounds l, F j (fun i => l i-j i)) =
      ∑ k ∈ Finset.range (m+1), ∑ j ∈ backgroundVectors N B k,
        ∑ q ∈ backgroundVectors N B (m-k), F j q := by
  rw [Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨⟨backgroundDegree p.2, p.2⟩, fun i => p.1 i-p.2 i⟩)
  · intro p hp
    obtain ⟨hl, hj⟩ := Finset.mem_sigma.mp hp
    have hlj := (mem_subBackgrounds p.1 p.2).mp hj
    have hdeg : backgroundDegree p.1 = m := (mem_backgroundVectors_iff N B m hm p.1).mp hl
    have he := backgroundDegree_sub_add p.1 p.2 hlj
    have hk : backgroundDegree p.2 ≤ m := by omega
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_sigma.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      · exact (mem_backgroundVectors_iff N B _ (le_trans hk hm) _).mpr rfl
    · apply (mem_backgroundVectors_iff N B _ (by omega) _).mpr
      change backgroundDegree (fun i => p.1 i-p.2 i) = m-backgroundDegree p.2
      omega
  · intro p hp q hq he
    obtain ⟨hlp, hjp⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hlq, hjq⟩ := Finset.mem_sigma.mp hq
    have hpj := (mem_subBackgrounds p.1 p.2).mp hjp
    have hqj := (mem_subBackgrounds q.1 q.2).mp hjq
    have heJ : p.2 = q.2 := congrArg (fun v => v.1.2) he
    have heQ : (fun i => p.1 i-p.2 i) = (fun i => q.1 i-q.2 i) := congrArg Sigma.snd he
    have heL : p.1 = q.1 := by
      funext i
      have hj := congrFun heJ i
      have hq := congrFun heQ i
      have hpi := hpj i
      have hqi := hqj i
      omega
    cases p
    cases q
    dsimp at heJ heL
    subst_vars
    rfl
  · intro p hp
    obtain ⟨hkj, hq⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hkj
    have hk' : p.1.1 ≤ m := by have := Finset.mem_range.mp hk; omega
    have hdegJ : backgroundDegree p.1.2 = p.1.1 :=
      (mem_backgroundVectors_iff N B _ (by omega) _).mp hj
    have hdegQ : backgroundDegree p.2 = m-p.1.1 :=
      (mem_backgroundVectors_iff N B _ (by omega) _).mp hq
    let l : Fin N → ℕ := fun i => p.1.2 i+p.2 i
    have hl : l ∈ backgroundVectors N B m := by
      apply (mem_backgroundVectors_iff N B m hm l).mpr
      change backgroundDegree l = m
      dsimp only [l]
      rw [backgroundDegree_add, hdegJ, hdegQ, Nat.add_sub_of_le hk']
    have hjl : p.1.2 ∈ subBackgrounds l := by
      apply (mem_subBackgrounds l _).mpr
      intro i
      dsimp only [l]
      omega
    refine ⟨⟨l, p.1.2⟩, Finset.mem_sigma.mpr ⟨hl, hjl⟩, ?_⟩
    apply Sigma.ext
    · apply Sigma.ext
      · exact hdegJ
      · rfl
    · apply heq_of_eq
      funext i
      dsimp only [l]
      omega
  · intro p hp
    rfl
lemma background_exponential_convolution {N B m : ℕ} (hm : m ≤ B)
    (t : Fin N → ℝ) (F G : (Fin N → ℕ) → ℝ) :
    (∑ l ∈ backgroundVectors N B m, (∏ i, t i^(l i)/(l i).factorial)*
      ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*F j*G (fun i => l i-j i)) =
    ∑ k ∈ Finset.range (m+1),
      (∑ j ∈ backgroundVectors N B k, (∏ i, t i^(j i)/(j i).factorial)*F j)*
      (∑ q ∈ backgroundVectors N B (m-k), (∏ i, t i^(q i)/(q i).factorial)*G q) := by
  conv_lhs => simp only [Finset.mul_sum]
  calc
    _ = ∑ l ∈ backgroundVectors N B m, ∑ j ∈ subBackgrounds l,
        ((∏ i, t i^(j i)/(j i).factorial)*F j)*
          ((∏ i, t i^(l i-j i)/(l i-j i).factorial)*G (fun i => l i-j i)) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      have he := background_binomial_split t l j ((mem_subBackgrounds l j).mp hj)
      linear_combination (F j*G (fun i => l i-j i))*he
    _ = ∑ k ∈ Finset.range (m+1), ∑ j ∈ backgroundVectors N B k,
        ∑ q ∈ backgroundVectors N B (m-k),
          ((∏ i, t i^(j i)/(j i).factorial)*F j)*((∏ i, t i^(q i)/(q i).factorial)*G q) :=
      sum_background_decompose hm (fun j q =>
        ((∏ i, t i^(j i)/(j i).factorial)*F j)*((∏ i, t i^(q i)/(q i).factorial)*G q))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      exact Finset.sum_mul_sum _ _ _ _
end WP
