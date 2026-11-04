import WPFormalization.Intersection.BackgroundSupport
/-! Exact collapse of the finite background sum to degree-two insertions at
the critical parameter. This proves the original endpoint normalization by
finite enumeration, without assuming a limiting recursion or continuity. -/
noncomputable section
namespace WP
lemma background_critical_collapse (N B m : ℕ) (hB : m ≤ B)
    (F : (Fin (N+1) → ℕ) → ℝ) :
    (∑ l ∈ backgroundVectors (N+1) B m, F l*
      ∏ i : Fin (N+1), (if i.val = 0 then 3 else 0 : ℝ)^(l i)/(l i).factorial) =
    F (Fin.cons m 0)*(3^m/(m.factorial : ℝ)) := by
  let star : Fin (N+1) → ℕ := Fin.cons m 0
  have hstar : star ∈ backgroundVectors (N+1) B m := by
    apply (mem_backgroundVectors_iff (N+1) B m hB star).mpr
    simp [star, Fin.sum_univ_succ]
  have hsweight : (∏ i : Fin (N+1), (if i.val = 0 then 3 else 0 : ℝ)^(star i)/
      (star i).factorial) = 3^m/(m.factorial : ℝ) := by
    simp [star, Fin.prod_univ_succ]
  calc
    _ = F star*(∏ i : Fin (N+1), (if i.val = 0 then 3 else 0 : ℝ)^(star i)/
        (star i).factorial) := by
      apply Finset.sum_eq_single star
      · intro l hl hls
        by_cases hzero : ∀ i : Fin N, l i.succ = 0
        · have hd : (∑ i : Fin (N+1), (i.val+1)*l i) = m :=
            (mem_backgroundVectors_iff (N+1) B m hB l).mp hl
          have hhead : l 0 = m := by simpa [Fin.sum_univ_succ, hzero] using hd
          have he : l = star := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [star, hhead]
            · simp [star, hzero]
          exact False.elim (hls he)
        · have he : ∃ i : Fin N, l i.succ ≠ 0 := by push Not at hzero; exact hzero
          obtain ⟨i, hi⟩ := he
          have hp : (∏ j : Fin (N+1), (if j.val = 0 then 3 else 0 : ℝ)^(l j)/(l j).factorial) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ i.succ)
            simp [hi]
          rw [hp, mul_zero]
      · intro hs
        exact False.elim (hs hstar)
    _ = _ := by rw [hsweight]
lemma backgroundDegrees_critical (N m : ℕ) :
    backgroundDegrees (Fin.cons m (0 : Fin N → ℕ)) = List.replicate m 2 := by
  simp [backgroundDegrees, List.finRange_succ, List.flatMap_map]
lemma finiteBackgroundAmplitude_critical (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (N B m : ℕ) (hB : m ≤ B) :
    finiteBackgroundAmplitude P g d B m
      (fun i : Fin (N+1) => if i.val = 0 then 3 else 0) =
    doubleWeight d * P.psi g (d ++ List.replicate m 2)*(3^m/(m.factorial : ℝ)) := by
  unfold finiteBackgroundAmplitude
  rw [background_critical_collapse N B m hB, backgroundDegrees_critical]
  simp only [List.map_replicate, Int.ofNat_eq_natCast, Nat.cast_ofNat]
  ring
lemma finiteBackgroundAmplitude_normalized_critical (P : PsiTheory) (g : ℕ)
    (d : List ℕ) (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length)
    (N B : ℕ) (hB : deficit g d ≤ B) :
    finiteBackgroundAmplitude P g (d.map Int.ofNat) B (deficit g d)
      (fun i : Fin (N+1) => if i.val = 0 then 3 else 0) = normalized P g d y₀ := by
  rw [finiteBackgroundAmplitude_critical P g _ N B _ hB]
  have hvalid : Stable g d.length ∧ d.sum ≤ dimension g d.length := ⟨hs, hd⟩
  simp only [normalized, ite_true, if_pos hvalid, pure, List.map_append,
    List.map_replicate, Int.ofNat_eq_natCast, Nat.cast_ofNat]
  simp [doubleWeight, List.map_map, Function.comp_def]
  ring
end WP
