import WPFormalization.Intersection.BackgroundMerging

/-! The exact finite-background DVV equation. Every summand is obtained from
`PsiTheory.dvv`, with the external, background-merging, nonseparating and
ordered separating contributions normalized by their actual background weights.
No shifted-recursion identity is assumed. -/
noncomputable section
namespace WP
lemma dvv_external_merge_cancel (P : PsiTheory) (g p : ℕ) (d e : List ℤ)
    (j : ℕ) (hj : j < d.length) :
    ((2*((d++e)[j]! : ℝ)+1)*
      weighted P.psi g (((p : ℤ)+(d++e)[j]!-1) :: (d++e).eraseIdx j))/doubleWeight e =
    (2*(d[j]! : ℝ)+1)*doubleWeight (((p : ℤ)+d[j]!-1) :: d.eraseIdx j)*
      P.psi g ((((p : ℤ)+d[j]!-1) :: d.eraseIdx j) ++ e) := by
  have hget : (d++e)[j]! = d[j]! := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hj]
  rw [hget, List.eraseIdx_append_of_lt_length hj]
  change ((2*(d[j]! : ℝ)+1)*
    weighted P.psi g (((p : ℤ)+d[j]!-1) :: d.eraseIdx j ++ e))/doubleWeight e = _
  rw [mul_div_assoc, weighted_append_cancel]
  ring
lemma dvv_background_merge_reindex (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) (j : ℕ) (hj : j < (backgroundDegrees l).length) :
    (2*((d ++ (backgroundDegrees l).map Int.ofNat)[d.length+j]! : ℝ)+1)*
      weighted P.psi g
        (((p : ℤ)+(d ++ (backgroundDegrees l).map Int.ofNat)[d.length+j]!-1) ::
          (d ++ (backgroundDegrees l).map Int.ofNat).eraseIdx (d.length+j)) =
    (((2*(backgroundDegrees l)[j]!+1 : ℕ) : ℝ))*
      weighted P.psi g ((((p : ℤ)+(backgroundDegrees l)[j]!-1) :: d) ++
        ((backgroundDegrees l).eraseIdx j).map Int.ofNat) := by
  have hget : (d ++ (backgroundDegrees l).map Int.ofNat)[d.length+j]! =
      ((backgroundDegrees l)[j]! : ℤ) := by
    simp only [List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by omega : d.length ≤ d.length+j), Nat.add_sub_cancel_left]
    simp [hj]
  rw [hget, List.eraseIdx_append_of_length_le (by omega : d.length ≤ d.length+j),
    Nat.add_sub_cancel_left, List.eraseIdx_map]
  push_cast
  rfl
lemma dvv_background_separating_cancel (P : PsiTheory) (g₁ g₂ : ℕ)
    (u v : ℤ) (d : List ℤ) {N : ℕ} (l : Fin N → ℕ) :
    (∑ K ∈ (Finset.range (d ++ (backgroundDegrees l).map Int.ofNat).length).powerset,
      weighted P.psi g₁ (u :: selected (d ++ (backgroundDegrees l).map Int.ofNat) K)*
      weighted P.psi g₂ (v :: selected (d ++ (backgroundDegrees l).map Int.ofNat)
        ((Finset.range (d ++ (backgroundDegrees l).map Int.ofNat).length) \ K))) /
        doubleWeight ((backgroundDegrees l).map Int.ofNat) =
    ∑ I ∈ (Finset.range d.length).powerset, ∑ j ∈ subBackgrounds l,
      (∏ i, ((l i).choose (j i) : ℝ))*
      (doubleWeight (u :: selected d I)*
        P.psi g₁ ((u :: selected d I) ++ (backgroundDegrees j).map Int.ofNat))*
      (doubleWeight (v :: selected d ((Finset.range d.length) \ I))*
        P.psi g₂ ((v :: selected d ((Finset.range d.length) \ I)) ++
          (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)) := by
  rw [sum_selected_append d ((backgroundDegrees l).map Int.ofNat)
    (fun x y => weighted P.psi g₁ (u :: x)*weighted P.psi g₂ (v :: y)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I hI
  have he := sum_selected_background l (fun x y =>
    weighted P.psi g₁ ((u :: selected d I) ++ x)*
      weighted P.psi g₂ ((v :: selected d ((Finset.range d.length) \ I)) ++ y))
  simp only [List.length_map]
  erw [he, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (∏ i, ((l i).choose (j i) : ℝ))*
        ((weighted P.psi g₁ ((u :: selected d I) ++ (backgroundDegrees j).map Int.ofNat)*
          weighted P.psi g₂ ((v :: selected d ((Finset.range d.length) \ I)) ++
            (backgroundDegrees (fun i => l i-j i)).map Int.ofNat)) /
          doubleWeight ((backgroundDegrees l).map Int.ofNat)) := by ring
    _ = _ := by
      rw [weighted_background_split_cancel P g₁ g₂ _ _ l j ((mem_subBackgrounds l j).mp hj)]
      ring
end WP

namespace WP
def backgroundExternalTerm (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) : ℝ :=
  ∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
    doubleWeight (((p : ℤ)+d[j]!-1) :: d.eraseIdx j)*
      P.psi g ((((p : ℤ)+d[j]!-1) :: d.eraseIdx j) ++ (backgroundDegrees l).map Int.ofNat)
def backgroundMergeTerm (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) : ℝ :=
  (∑ j ∈ Finset.range (backgroundDegrees l).length,
    (((2*(backgroundDegrees l)[j]!+1 : ℕ) : ℝ))*
      weighted P.psi g ((((p : ℤ)+(backgroundDegrees l)[j]!-1) :: d) ++
        ((backgroundDegrees l).eraseIdx j).map Int.ofNat)) /
    doubleWeight ((backgroundDegrees l).map Int.ofNat)
def backgroundNonseparatingTerm (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) : ℝ :=
  if g = 0 then 0 else (1/2 : ℝ)*∑ u ∈ Finset.range (p-1),
    doubleWeight ((u : ℤ) :: ((p : ℤ)-2-u) :: d)*
      P.psi (g-1) (((u : ℤ) :: ((p : ℤ)-2-u) :: d) ++ (backgroundDegrees l).map Int.ofNat)
def backgroundSeparatingTerm (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) : ℝ :=
  (1/2 : ℝ)*∑ u ∈ Finset.range (p-1), ∑ g₁ ∈ Finset.range (g+1),
    ∑ I ∈ (Finset.range d.length).powerset, ∑ j ∈ subBackgrounds l,
      (∏ i, ((l i).choose (j i) : ℝ))*
      (doubleWeight ((u : ℤ) :: selected d I)*
        P.psi g₁ (((u : ℤ) :: selected d I) ++ (backgroundDegrees j).map Int.ofNat))*
      (doubleWeight (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I))*
        P.psi (g-g₁) ((((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)) ++
          (backgroundDegrees (fun i => l i-j i)).map Int.ofNat))
lemma dvv_per_background (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    (hd : ∀ k ∈ d, 0 ≤ k) (hh : 2 ≤ complexity g (d.length+1))
    {N : ℕ} (l : Fin N → ℕ) :
    doubleWeight ((p : ℤ) :: d)*P.psi g (((p : ℤ) :: d) ++ (backgroundDegrees l).map Int.ofNat) =
      backgroundExternalTerm P g p d l + backgroundMergeTerm P g p d l +
      backgroundNonseparatingTerm P g p d l + backgroundSeparatingTerm P g p d l := by
  let b := (backgroundDegrees l).map Int.ofNat
  have hd' : ∀ k ∈ d++b, 0 ≤ k := by
    intro k hk
    rcases List.mem_append.mp hk with he | he
    · exact hd k he
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
      exact Int.natCast_nonneg j
  have hh' : 2 ≤ complexity g ((d++b).length+1) := by
    simp only [List.length_append]
    unfold complexity at hh ⊢
    omega
  have hv := P.dvv g p (d++b) hd' hh'
  have he : weighted P.psi g (((p : ℤ) :: d)++b) = dvvRHS P.psi g p (d++b) := hv
  have heD := congrArg (fun x : ℝ => x/doubleWeight b) he
  rw [weighted_append_cancel] at heD
  have hm : (∑ j ∈ Finset.range (d++b).length, (2*((d++b)[j]! : ℝ)+1)*
      weighted P.psi g (((p : ℤ)+(d++b)[j]!-1) :: (d++b).eraseIdx j))/doubleWeight b =
      backgroundExternalTerm P g p d l + backgroundMergeTerm P g p d l := by
    simp only [List.length_append]
    rw [Finset.sum_range_add, add_div]
    apply congrArg₂ (fun x y : ℝ => x+y)
    · unfold backgroundExternalTerm
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      exact dvv_external_merge_cancel P g p d b j (Finset.mem_range.mp hj)
    · unfold backgroundMergeTerm
      apply congrArg (fun x : ℝ => x/doubleWeight b)
      simp only [b, List.length_map]
      apply Finset.sum_congr rfl
      intro j hj
      exact dvv_background_merge_reindex P g p d l j (Finset.mem_range.mp hj)
  have hn : (if g = 0 then 0 else (1/2 : ℝ)*∑ u ∈ Finset.range (p-1),
      weighted P.psi (g-1) ((u : ℤ) :: ((p : ℤ)-2-u) :: d++b))/doubleWeight b =
      backgroundNonseparatingTerm P g p d l := by
    unfold backgroundNonseparatingTerm
    by_cases hg : g = 0
    · simp [hg]
    · simp only [hg, ite_false]
      rw [mul_div_assoc, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      exact weighted_append_cancel P (g-1) ((u : ℤ) :: ((p : ℤ)-2-u) :: d) b
  have hs : ((1/2 : ℝ)*∑ u ∈ Finset.range (p-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ K ∈ (Finset.range (d++b).length).powerset,
        weighted P.psi g₁ ((u : ℤ) :: selected (d++b) K)*
        weighted P.psi (g-g₁) (((p : ℤ)-2-u) :: selected (d++b) ((Finset.range (d++b).length) \ K))) /
        doubleWeight b = backgroundSeparatingTerm P g p d l := by
    unfold backgroundSeparatingTerm
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g₁ hg₁
    exact dvv_background_separating_cancel P g₁ (g-g₁) u ((p : ℤ)-2-u) d l
  unfold dvvRHS at heD
  simp only [add_div] at heD
  simp only [List.cons_append] at hn heD
  rw [hm, hn, hs] at heD
  simpa only [List.cons_append, b] using heD
end WP

namespace WP
lemma finiteBackgroundAmplitude_eq_sum (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B k : ℕ) (t : Fin N → ℝ) :
    finiteBackgroundAmplitude P g d B k t =
      ∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
        (doubleWeight d*P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)) := by
  unfold finiteBackgroundAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring
lemma finiteBackgroundAmplitude_cauchy (P : PsiTheory) (g₁ g₂ : ℕ) (d₁ d₂ : List ℤ)
    {N : ℕ} (B k : ℕ) (hk : k ≤ B) (t : Fin N → ℝ) :
    (∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
      ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
        (doubleWeight d₁*P.psi g₁ (d₁ ++ (backgroundDegrees j).map Int.ofNat))*
        (doubleWeight d₂*P.psi g₂ (d₂ ++ (backgroundDegrees (fun i => l i-j i)).map Int.ofNat))) =
    ∑ r ∈ Finset.range (k+1), finiteBackgroundAmplitude P g₁ d₁ B r t*
      finiteBackgroundAmplitude P g₂ d₂ B (k-r) t := by
  have he := background_exponential_convolution hk t
    (fun j => doubleWeight d₁*P.psi g₁ (d₁ ++ (backgroundDegrees j).map Int.ofNat))
    (fun j => doubleWeight d₂*P.psi g₂ (d₂ ++ (backgroundDegrees j).map Int.ofNat))
  rw [he]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  · symm
    exact finiteBackgroundAmplitude_eq_sum P g₁ d₁ B r t
  · symm
    exact finiteBackgroundAmplitude_eq_sum P g₂ d₂ B (k-r) t
lemma sum_background_external_term (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (B k : ℕ) (t : Fin N → ℝ) :
    (∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
      backgroundExternalTerm P g p d l) =
    ∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
      finiteBackgroundAmplitude P g (((p : ℤ)+d[j]!-1) :: d.eraseIdx j) B k t := by
  unfold backgroundExternalTerm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteBackgroundAmplitude_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring
lemma sum_background_nonseparating_term (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (B k : ℕ) (t : Fin N → ℝ) :
    (∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
      backgroundNonseparatingTerm P g p d l) =
    if g = 0 then 0 else (1/2 : ℝ)*∑ u ∈ Finset.range (p-1),
      finiteBackgroundAmplitude P (g-1) ((u : ℤ) :: ((p : ℤ)-2-u) :: d) B k t := by
  unfold backgroundNonseparatingTerm
  by_cases hg : g = 0
  · simp [hg]
  · simp only [hg, ite_false, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [finiteBackgroundAmplitude_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
lemma sum_background_separating_term (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (B k : ℕ) (hk : k ≤ B) (t : Fin N → ℝ) :
    (∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
      backgroundSeparatingTerm P g p d l) =
    (1/2 : ℝ)*∑ u ∈ Finset.range (p-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset, ∑ r ∈ Finset.range (k+1),
        finiteBackgroundAmplitude P g₁ ((u : ℤ) :: selected d I) B r t*
        finiteBackgroundAmplitude P (g-g₁) (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)) B (k-r) t := by
  unfold backgroundSeparatingTerm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g₁ hg₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  calc
    _ = (1/2 : ℝ)*(∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
        ∑ j ∈ subBackgrounds l, (∏ i, ((l i).choose (j i) : ℝ))*
          (doubleWeight ((u : ℤ) :: selected d I)*
            P.psi g₁ (((u : ℤ) :: selected d I) ++ (backgroundDegrees j).map Int.ofNat))*
          (doubleWeight (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I))*
            P.psi (g-g₁) ((((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)) ++
              (backgroundDegrees (fun i => l i-j i)).map Int.ofNat))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [finiteBackgroundAmplitude_cauchy P g₁ (g-g₁) _ _ B k hk t, Finset.mul_sum]
def finiteBackgroundChildren (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (B k : ℕ) (t : Fin N → ℝ) : ℝ :=
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
    finiteBackgroundAmplitude P g (((p : ℤ)+d[j]!-1) :: d.eraseIdx j) B k t) +
  (if g = 0 then 0 else (1/2 : ℝ)*∑ u ∈ Finset.range (p-1),
    finiteBackgroundAmplitude P (g-1) ((u : ℤ) :: ((p : ℤ)-2-u) :: d) B k t) +
  (1/2 : ℝ)*∑ u ∈ Finset.range (p-1), ∑ g₁ ∈ Finset.range (g+1),
    ∑ I ∈ (Finset.range d.length).powerset, ∑ r ∈ Finset.range (k+1),
      finiteBackgroundAmplitude P g₁ ((u : ℤ) :: selected d I) B r t*
      finiteBackgroundAmplitude P (g-g₁) (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)) B (k-r) t
def finiteBackgroundMerges (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    {N : ℕ} (B k : ℕ) (t : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, if i.val+1 ≤ k then t i/(oddFactorial (i.val+1) : ℝ)*
    finiteBackgroundAmplitude P g (((p : ℤ)+(i.val+2)-1) :: d) B (k-(i.val+1)) t else 0
lemma finiteBackgroundAmplitude_dvv (P : PsiTheory) (g p : ℕ) (d : List ℤ)
    (hd : ∀ j ∈ d, 0 ≤ j) (hh : 2 ≤ complexity g (d.length+1))
    {N : ℕ} (B k : ℕ) (hk : k ≤ B) (t : Fin N → ℝ) :
    finiteBackgroundAmplitude P g ((p : ℤ) :: d) B k t =
      finiteBackgroundChildren P g p d B k t + finiteBackgroundMerges P g p d B k t := by
  rw [finiteBackgroundAmplitude_eq_sum]
  simp_rw [dvv_per_background P g p d hd hh]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_background_external_term, sum_background_nonseparating_term,
    sum_background_separating_term P g p d B k hk t]
  have he : (∑ l ∈ backgroundVectors N B k, (∏ i, t i^(l i)/(l i).factorial)*
      backgroundMergeTerm P g p d l) = finiteBackgroundMerges P g p d B k t := by
    unfold backgroundMergeTerm finiteBackgroundMerges
    exact background_merging_operator P g p d B k hk t
  rw [he]
  unfold finiteBackgroundChildren
  ring
end WP
