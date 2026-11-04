import WPFormalization.Intersection.CriticalBackground
import WPFormalization.Analysis.DilatonCoefficients

/-! The shifted dilaton identity by exact finite background cancellation.

A coordinate increment adds one insertion to the background degree list up to
permutation. Exponential-weight reindexing then identifies every higher-time
insertion with its corresponding background multiplicity. Summing these
multiplicities cancels the background length in the classical dilaton equation.
The final normalization is the original finite amplitude, including the
zero-background stable cases. No analytic continuation or limiting identity is
assumed in this proof.
-/
noncomputable section
namespace WP
lemma backgroundDegrees_update_perm {N : ℕ} (l : Fin N → ℕ) (i : Fin N) :
    (backgroundDegrees (Function.update l i (l i+1))).Perm
      ((i.val+2) :: backgroundDegrees l) := by
  apply List.perm_iff_count.mpr
  intro a
  simp only [backgroundDegrees, List.count_flatMap, List.count_cons]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq, List.finRange, List.map_ofFn, List.sum_ofFn]
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add Finset.univ (fun j => _) (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : (∑ j ∈ Finset.univ.erase i,
      (if j.val+2 = a then Function.update l i (l i+1) j else 0)) =
      ∑ j ∈ Finset.univ.erase i, (if j.val+2 = a then l j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  split_ifs <;> omega
lemma psi_background_raise (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) (i : Fin N) (hi : 0 < l i) :
    P.psi g (((i.val+2 : ℕ) : ℤ) :: d ++
      (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) =
    P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) := by
  have hbg := backgroundDegrees_update_perm (Function.update l i (l i-1)) i
  rw [update_lower_raise l i hi] at hbg
  apply P.symmetry
  have hm := hbg.symm.map Int.ofNat
  have ha := List.Perm.append_left d hm
  exact List.perm_middle.symm.trans ha

lemma background_raise_psi (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N B M : ℕ} (i : Fin N) (hi : i.val+1 ≤ M) (hB : M ≤ B)
    (t : Fin N → ℝ) :
    t i * (∑ l ∈ backgroundVectors N B (M-(i.val+1)),
      (∏ j : Fin N, t j^(l j)/(l j).factorial)*
        P.psi g (((i.val+2 : ℕ) : ℤ) :: d ++ (backgroundDegrees l).map Int.ofNat)) =
    ∑ l ∈ backgroundVectors N B M, (l i : ℝ)*
      (∏ j : Fin N, t j^(l j)/(l j).factorial)*
        P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) := by
  have he := sum_background_raise i (k := M-(i.val+1))
    (show M-(i.val+1)+(i.val+1) ≤ B by omega) t
    (fun l => P.psi g (((i.val+2 : ℕ) : ℤ) :: d ++ (backgroundDegrees l).map Int.ofNat))
  rw [Nat.sub_add_cancel hi] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hli : 0 < l i
  · rw [psi_background_raise P g d l i hli]
  · have hz : l i = 0 := by omega
    simp [hz]

lemma background_dilaton (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hs : Stable g d.length) (M B : ℕ) (hB : M ≤ B) (t : Fin M → ℝ) :
    (2*(g : ℝ)-2+d.length) *
      (∑ l ∈ backgroundVectors M B M,
        (∏ i : Fin M, t i^(l i)/(l i).factorial)*
          P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)) =
    (∑ l ∈ backgroundVectors M B M,
      (∏ i : Fin M, t i^(l i)/(l i).factorial)*
        P.psi g (1 :: d ++ (backgroundDegrees l).map Int.ofNat)) -
    ∑ i : Fin M, t i *
      (∑ l ∈ backgroundVectors M B (M-(i.val+1)),
        (∏ j : Fin M, t j^(l j)/(l j).factorial)*
          P.psi g (((i.val+2 : ℕ) : ℤ) :: d ++ (backgroundDegrees l).map Int.ofNat)) := by
  have hraise (i : Fin M) := background_raise_psi P g d i (show i.val+1 ≤ M by omega) hB t
  simp_rw [hraise]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hstable : Stable g (d ++ (backgroundDegrees l).map Int.ofNat).length := by
    simp only [List.length_append, List.length_map]
    unfold Stable at *
    omega
  simp only [List.cons_append]
  rw [P.dilaton g _ hstable]
  have hlen : ((backgroundDegrees l).length : ℝ) = ∑ i : Fin M, (l i : ℝ) := by
    rw [backgroundDegrees_length]
    push_cast
    rfl
  simp only [List.length_append, List.length_map, Nat.cast_add]
  rw [hlen]
  ring
lemma normalized_zero_as_background (P : PsiTheory) (g p : ℕ)
    (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    normalized P g (List.replicate p 0) Y =
      ∑ l ∈ backgroundVectors (dimension g p) (dimension g p) (dimension g p),
        (∏ i : Fin (dimension g p),
          ((-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y)^(l i)/(l i).factorial)*
          P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat) := by
  have hd : (List.replicate p 0).sum ≤ dimension g (List.replicate p 0).length := by simp
  have hdef : deficit g (List.replicate p 0) = dimension g p := by simp [deficit]
  have hn := finiteBackgroundAmplitude_normalized_interior_of_le P g (List.replicate p 0)
    Y hY (by simpa using hs) hd (dimension g p) (dimension g p)
    (by rw [hdef]) (by rw [hdef])
  rw [hdef] at hn
  rw [← hn]
  simp only [finiteBackgroundAmplitude, List.map_replicate, Int.ofNat_eq_natCast, Nat.cast_zero,
    doubleWeight, List.map_replicate, Int.toNat_zero, oddFactorial, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.mul_zero, zero_add, Nat.cast_one, List.prod_replicate,
    one_pow, one_mul]
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma normalized_mark_as_background (P : PsiTheory) (g p : ℕ)
    (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀)
    (d : ℕ) (hd : 1 ≤ d) (hdim : d ≤ dimension g p+1) :
    normalized P g (d :: List.replicate p 0) Y =
      (oddFactorial d : ℝ) *
      ∑ l ∈ backgroundVectors (dimension g p) (dimension g p) (dimension g p+1-d),
        (∏ i : Fin (dimension g p),
          ((-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y)^(l i)/(l i).factorial)*
          P.psi g ((d : ℤ) :: List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat) := by
  have hs' : Stable g (p+1) := by unfold Stable at *; omega
  have hdim' : dimension g (p+1) = dimension g p+1 := by
    unfold dimension Stable at *
    omega
  have hd' : (d :: List.replicate p 0).sum ≤ dimension g (d :: List.replicate p 0).length := by
    simpa [hdim'] using hdim
  have hdef : deficit g (d :: List.replicate p 0) = dimension g p+1-d := by simp [deficit, hdim']
  have hn := finiteBackgroundAmplitude_normalized_interior_of_le P g (d :: List.replicate p 0)
    Y hY (by simpa using hs') hd' (dimension g p) (dimension g p)
    (by rw [hdef]; omega) (by rw [hdef]; omega)
  rw [hdef] at hn
  rw [← hn]
  simp only [finiteBackgroundAmplitude, List.map_cons, List.map_replicate, Int.ofNat_eq_natCast,
    Nat.cast_zero, doubleWeight, List.map_cons, List.map_replicate, Int.toNat_natCast,
    Int.toNat_zero, List.prod_cons, List.prod_replicate]
  have hzero : oddFactorial 0 = 1 := by norm_num [oddFactorial]
  rw [hzero]
  simp only [Nat.cast_one, one_pow, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  ring
lemma dilaton_sum_split (M : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ Finset.range (M+2), if 1 ≤ d then F d else 0) =
      F 1+∑ i : Fin M, F (i.val+2) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => F (k+2)) M]
  simp [Finset.sum_range_succ', Nat.add_left_comm, add_comm]

lemma shifted_dilaton_proof (P : PsiTheory) (g p : ℕ) (hst : Stable g p)
    (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    (complexity g p : ℝ) * normalized P g (List.replicate p 0) Y =
      ∑ d ∈ Finset.range (dimension g (p+1)+1),
        if 1 ≤ d then
          ((iteratedDeriv d X Y).re * r Y^(d-1)/(a Y*oddFactorial d)) *
            normalized P g (d :: List.replicate p 0) Y else 0 := by
  let M := dimension g p
  let t : Fin M → ℝ := fun i =>
    (-(iteratedDeriv (i.val+2) X Y).re)*r Y^(i.val+1)/a Y
  have hdim : dimension g (p+1) = M+1 := by
    unfold M dimension Stable at *
    omega
  rw [hdim, show M+1+1 = M+2 by omega, dilaton_sum_split]
  have hc : (complexity g p : ℝ) = 2*(g : ℝ)-2+p := by
    have hn : 2 ≤ 2*g+p := by unfold Stable at hst; omega
    unfold complexity
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [hc, normalized_zero_as_background P g p hst Y hY]
  have hfirst :
      ((iteratedDeriv 1 X Y).re*r Y^(1-1)/(a Y*oddFactorial 1)) *
        normalized P g (1 :: List.replicate p 0) Y =
      ∑ l ∈ backgroundVectors M M M,
        (∏ i : Fin M, t i^(l i)/(l i).factorial)*
          P.psi g (1 :: List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat) := by
    rw [normalized_mark_as_background P g p hst Y hY 1 (by omega) (by omega)]
    rw [show dimension g p+1-1 = M by simp [M]]
    have hone : oddFactorial 1 = 3 := by norm_num [oddFactorial, Finset.prod_range_succ]
    have ha := a_ne_zero Y hY
    simp only [iteratedDeriv_one, a, Nat.sub_self, pow_zero, mul_one, hone, Nat.cast_ofNat]
    change (a Y/(a Y*3))*(3*(∑ l ∈ backgroundVectors M M M,
      (∏ i : Fin M, t i^(l i)/(l i).factorial)*
        P.psi g (1 :: List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat))) = _
    have hcoef : a Y/(a Y*3)*3 = 1 := by field_simp [ha]
    rw [← mul_assoc,hcoef,one_mul]
  rw [hfirst]
  have hrest (i : Fin M) :
      ((iteratedDeriv (i.val+2) X Y).re*r Y^(i.val+2-1)/(a Y*oddFactorial (i.val+2))) *
        normalized P g ((i.val+2) :: List.replicate p 0) Y =
      -t i * (∑ l ∈ backgroundVectors M M (M-(i.val+1)),
        (∏ j : Fin M, t j^(l j)/(l j).factorial)*
          P.psi g (((i.val+2 : ℕ) : ℤ) :: List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)) := by
    rw [normalized_mark_as_background P g p hst Y hY (i.val+2) (by omega) (by omega)]
    have he : M+1-(i.val+2) = M-(i.val+1) := by omega
    rw [he]
    have ho : (oddFactorial (i.val+2) : ℝ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero (i.val+2)
    have ha := a_ne_zero Y hY
    have hp : i.val+2-1 = i.val+1 := by omega
    rw [hp]
    dsimp [t]
    field_simp [ha,ho]
    ring
  simp_rw [hrest, neg_mul]
  rw [Finset.sum_neg_distrib]
  rw [← sub_eq_add_neg]
  simpa only [List.length_replicate,t,neg_mul] using
    background_dilaton P g (List.replicate p 0) (by simpa using hst) M M le_rfl t

end WP
