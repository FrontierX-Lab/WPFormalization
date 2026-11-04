import WPFormalization.Intersection.CanonicalBackground
/-! The exact positive recursion from finite-background DVV.
The canonical times are fixed by the actual kernel. The proof handles the
full closed parameter interval, derives every truncated kernel-operator equation,
and applies the proved finite inverse convolution. -/
noncomputable section
namespace WP
lemma sum_fin_truncated (N k : ℕ) (hk : k ≤ N) (F : ℕ → ℝ) :
    (∑ i : Fin N, if i.val+1 ≤ k then F i.val else 0) = ∑ j ∈ Finset.range k, F j := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj he
    exact Fin.ext he
  · intro j hj
    have hkj := Finset.mem_range.mp hj
    refine ⟨⟨j, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i hi
    rfl
lemma finiteBackgroundAmplitude_normalized_of_degree (P : PsiTheory) (g : ℕ)
    (d : List ℕ) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (hs : Stable g d.length)
    (N B k : ℕ) (hNp : 0 < N) (hN : k ≤ N) (hB : k ≤ B)
    (hd : d.sum+k = dimension g d.length) :
    finiteBackgroundAmplitude P g (d.map Int.ofNat) B k
      (fun i : Fin N => normalizedBackgroundTime Y i.val) = normalized P g d Y := by
  have hle : d.sum ≤ dimension g d.length := by omega
  have hdef : deficit g d = k := by unfold deficit; omega
  have he := finiteBackgroundAmplitude_normalized_canonical P g d Y hY hs hle N B hNp
    (by rw [hdef]; exact hN) (by rw [hdef]; exact hB)
  rw [hdef] at he
  exact he
lemma normalized_kernel_operator (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ)
    (hh : 2 ≤ complexity g (d.length+1))
    (hd : (pivot :: d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀)
    (s : ℕ) (hs : s ≤ deficit g (pivot :: d)) :
    (∑ j ∈ Finset.range (deficit g (pivot :: d)-s+1), realCoeff (barK Y) j*
      normalized P g ((pivot+(s+j)) :: d) Y) = normalizedChildren P g (pivot+s) (d.map Int.ofNat) Y := by
  let m := deficit g (pivot :: d)
  let N := m+1
  let k := m-s
  let t : Fin N → ℝ := fun i => normalizedBackgroundTime Y i.val
  let U : ℕ → ℝ := fun j => normalized P g ((pivot+j) :: d) Y
  let V : ℕ → ℝ := fun j => normalizedChildren P g (pivot+j) (d.map Int.ofNat) Y
  have hs' : s ≤ m := hs
  have hNp : 0 < N := by dsimp [N]; omega
  have hkN : k ≤ N := by dsimp [k, N]; omega
  have hkB : k ≤ m := by dsimp [k]; omega
  have hst : Stable g (d.length+1) := by unfold complexity at hh; unfold Stable; omega
  have hm : (pivot :: d).sum+m = dimension g (d.length+1) := by
    simpa only [m, deficit, List.length_cons] using Nat.add_sub_of_le hd
  have hdegree (j : ℕ) (hj : j ≤ m) :
      ((pivot+j) :: d).sum+(m-j) = dimension g (d.length+1) := by
    simp only [List.sum_cons] at hm ⊢
    omega
  have hnorm (j : ℕ) (hj : j ≤ m) :
      finiteBackgroundAmplitude P g (((pivot+j) :: d).map Int.ofNat) m (m-j) t = U j := by
    exact finiteBackgroundAmplitude_normalized_of_degree P g ((pivot+j) :: d) Y hY
      (by simpa using hst) N m (m-j) hNp (by omega) (by omega) (by simpa using hdegree j hj)
  have hparent : finiteBackgroundAmplitude P g (((pivot+s : ℕ) : ℤ) :: d.map Int.ofNat) m k t = U s := by
    simpa only [List.map_cons, Int.ofNat_eq_natCast] using hnorm s hs'
  have hdim : (((pivot+s : ℕ) : ℤ) :: d.map Int.ofNat).sum+(k : ℤ) =
      3*(g : ℤ)-3+(((pivot+s : ℕ) : ℤ) :: d.map Int.ofNat).length := by
    have he := congrArg (fun j : ℕ => (j : ℤ)) (hdegree s hs')
    rw [dimension_cast_of_stable g (d.length+1) hst] at he
    simpa only [List.sum_cons, List.length_cons, List.length_map, sum_map_int,
      Nat.cast_add, Nat.cast_one] using he
  have hchildren : finiteBackgroundChildren P g (pivot+s) (d.map Int.ofNat) m k t = V s :=
    finiteBackgroundChildren_normalized P g (pivot+s) (d.map Int.ofNat) Y hY N m k hNp hkN hkB hdim
  have hposd : ∀ j ∈ d.map Int.ofNat, 0 ≤ j := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    exact Int.natCast_nonneg i
  have hdvv := finiteBackgroundAmplitude_dvv P g (pivot+s) (d.map Int.ofNat) hposd
    (by simpa using hh) m k hkB t
  rw [hparent, hchildren] at hdvv
  have hmerge : finiteBackgroundMerges P g (pivot+s) (d.map Int.ofNat) m k t =
      -(∑ j ∈ Finset.range k, realCoeff (barK Y) (j+1)*U (s+(j+1))) := by
    unfold finiteBackgroundMerges
    have hpoint (i : Fin N) :
        (if i.val+1 ≤ k then t i/(oddFactorial (i.val+1) : ℝ)*
          finiteBackgroundAmplitude P g ((((pivot+s : ℕ) : ℤ)+(i.val+2)-1) :: d.map Int.ofNat)
            m (k-(i.val+1)) t else 0) =
        if i.val+1 ≤ k then (-realCoeff (barK Y) (i.val+1))*U (s+(i.val+1)) else 0 := by
      by_cases hi : i.val+1 ≤ k
      · rw [if_pos hi, if_pos hi]
        have hswi : s+(i.val+1) ≤ m := by dsimp [k] at hi; omega
        have hl : ((((pivot+s : ℕ) : ℤ)+(i.val+2)-1) :: d.map Int.ofNat) =
            ((pivot+(s+(i.val+1))) :: d).map Int.ofNat := by
          simp only [List.map_cons, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
          congr 1
          omega
        have hres : k-(i.val+1) = m-(s+(i.val+1)) := by dsimp [k]; omega
        rw [hl, hres, hnorm (s+(i.val+1)) hswi]
        have hc : t i/(oddFactorial (i.val+1) : ℝ) = -realCoeff (barK Y) (i.val+1) := by
          dsimp only [t]
          rw [realCoeff_barK_succ_time]
          ring
        rw [hc]
      · simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => hpoint i),
      sum_fin_truncated N k hkN (fun j => -realCoeff (barK Y) (j+1)*U (s+(j+1)))]
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [hmerge] at hdvv
  have hzero : realCoeff (barK Y) 0 = 1 := by
    simp [realCoeff, coeff, barK_zero_closed Y hY]
  change (∑ j ∈ Finset.range (k+1), realCoeff (barK Y) j*U (s+j)) = V s
  rw [Finset.sum_range_succ']
  simp only [hzero, Nat.add_zero, one_mul]
  linarith
lemma normalized_positive_convolution (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ)
    (hh : 2 ≤ complexity g (d.length+1))
    (hd : (pivot :: d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (pivot :: d) Y =
      ∑ l ∈ Finset.range (deficit g (pivot :: d)+1), theta Y l*
        normalizedChildren P g (pivot+l) (d.map Int.ofNat) Y := by
  have he := normalized_kernel_finite_inversion Y hY (deficit g (pivot :: d))
    (fun l => normalized P g ((pivot+l) :: d) Y)
    (fun l => normalizedChildren P g (pivot+l) (d.map Int.ofNat) Y)
    (fun s hs => normalized_kernel_operator P g pivot d Y hh hd hY s hs)
  simpa only [Nat.add_zero] using he
end WP
