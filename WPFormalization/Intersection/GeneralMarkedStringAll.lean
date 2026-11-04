import WPFormalization.Intersection.GeneralMarkedString
noncomputable section
namespace WP
lemma shifted_unweighted_excess (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hd : dimension g d.length < d.sum) (Y : ℝ) :
    shifted P g d Y / externalOddWeight d = 0 := by
  simp [shifted, Nat.not_le.mpr hd]
lemma shifted_unweighted_top_degree (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum = dimension g d.length) (Y : ℝ) :
    shifted P g d Y / externalOddWeight d = pure P g d / a Y ^ complexity g d.length := by
  rw [shifted_div_odd_eq_markedRaw_diagonal P g d hs hd.le]
  have hm : deficit g d = 0 := by simp [deficit, hd]
  rw [hm]
  simp [markedRawAmplitude, backgroundVectors, backgroundDegrees, pure]
end WP
namespace WP
lemma pure_external_string (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) :
    pure P g (0::d) = ∑ j ∈ Finset.range d.length,
      if 0 < d[j]! then pure P g (d.set j (d[j]!-1)) else 0 := by
  have he := P.string g (d.map Int.ofNat) (by simpa using hs)
  simp only [List.length_map] at he
  change P.psi g ((0::d).map Int.ofNat) = _
  simp only [List.map_cons, Int.ofNat_eq_natCast, Nat.cast_zero]
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hget : (d.map Int.ofNat)[j]! = (d[j]!:ℤ) := by simp [hj']
  rw [hget]
  split_ifs with hpos
  · have hcast : Int.ofNat (d[j]!-1) = (d[j]!:ℤ)-1 := by
      change ((d[j]!-1:ℕ):ℤ) = (d[j]!:ℤ)-1
      omega
    simp only [pure, List.map_set, hcast]
  · have hz : d[j]! = 0 := by omega
    rw [hz]
    apply P.vanish
    exact Or.inr (Or.inl ⟨-1, by simpa using List.mem_set (by simpa using hj') (-1:ℤ), by norm_num⟩)

lemma shifted_unweighted_marked_hasDerivAt_all (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (Y : ℝ) (ha : a Y ≠ 0) :
    HasDerivAt (fun y : ℝ => shifted P g d y / externalOddWeight d)
      (a Y*(shifted P g (0::d) Y / externalOddWeight (0::d)) -
        ∑ j ∈ Finset.range d.length, if 0 < d[j]! then
          shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) else 0) Y := by
  by_cases hd : d.sum ≤ dimension g d.length
  · exact shifted_unweighted_marked_hasDerivAt P g d hs hd Y ha
  have hdim : dimension g (0::d).length = dimension g d.length+1 := by
    simp only [List.length_cons]
    unfold dimension Stable at *
    omega
  have hs0 : Stable g (0::d).length := by
    simp only [List.length_cons]
    unfold Stable at *
    omega
  have hc : complexity g (0::d).length = complexity g d.length+1 := by
    simp only [List.length_cons]
    unfold complexity Stable at *
    omega
  have hfun : (fun y : ℝ => shifted P g d y / externalOddWeight d) = fun _ => 0 :=
    funext (shifted_unweighted_excess P g d (by omega))
  rw [hfun]
  by_cases he : d.sum = dimension g d.length+1
  · have he0 : (0::d).sum = dimension g (0::d).length := by
      calc
        (0::d).sum = d.sum := by simp
        _ = dimension g d.length+1 := he
        _ = dimension g (0::d).length := hdim.symm
    rw [shifted_unweighted_top_degree P g (0::d) hs0 he0 Y,hc]
    have hsum : (∑ j ∈ Finset.range d.length, if 0 < d[j]! then
          shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) else 0) =
        pure P g (0::d) / a Y ^ complexity g d.length := by
      rw [pure_external_string P g d hs,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs with hpos
      · have hlow := lower_entry_sum d j (Finset.mem_range.mp hj) hpos
        have heq : (d.set j (d[j]!-1)).sum = dimension g (d.set j (d[j]!-1)).length := by
          simp only [List.length_set]
          omega
        simpa only [List.length_set] using shifted_unweighted_top_degree P g _
          (by simpa only [List.length_set] using hs) heq Y
      · simp
    rw [hsum,pow_succ]
    have hz : a Y * (pure P g (0::d) / (a Y ^ complexity g d.length * a Y)) -
        pure P g (0::d) / a Y ^ complexity g d.length = 0 := by field_simp;ring
    rw [hz]
    exact hasDerivAt_const Y 0
  · rw [shifted_unweighted_excess P g (0::d) (by simp only [List.sum_cons,zero_add,hdim];omega) Y,mul_zero]
    have hsum : (∑ j ∈ Finset.range d.length, if 0 < d[j]! then
          shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      split_ifs with hpos
      · have hlow := lower_entry_sum d j (Finset.mem_range.mp hj) hpos
        exact shifted_unweighted_excess P g _ (by simp only [List.length_set];omega) Y
      · rfl
    rw [hsum,sub_self]
    exact hasDerivAt_const Y 0
end WP
namespace WP
lemma shifted_external_analyticAt (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (Y : ℝ) (ha : a Y ≠ 0) : AnalyticAt ℝ (fun y => shifted P g d y / externalOddWeight d) Y := by
  by_cases hv : Stable g d.length ∧ d.sum ≤ dimension g d.length
  · have hf : (fun y => shifted P g d y / externalOddWeight d) =
        fun y => markedRawAmplitude P g (d.map Int.ofNat) (deficit g d) (deficit g d) (deficit g d)
          (a y) (fun i => -(iteratedDeriv (i.val+2) X y).re) :=
      funext (shifted_div_odd_eq_markedRaw_diagonal P g d hv.1 hv.2)
    rw [hf]
    unfold markedRawAmplitude
    have hjet (k : ℕ) : AnalyticAt ℝ (fun t : ℝ => (iteratedDeriv k X t).re) Y :=
      ((iteratedDeriv_X_differentiable k).analyticAt (Y:ℂ)).re_ofReal
    have haa : AnalyticAt ℝ a Y := by
      change AnalyticAt ℝ (fun t : ℝ => (deriv X t).re) Y
      simpa only [iteratedDeriv_one] using hjet 1
    apply Finset.analyticAt_fun_sum
    intro l hl
    apply AnalyticAt.div
    · apply AnalyticAt.mul analyticAt_const
      apply Finset.analyticAt_fun_prod
      intro i hi
      convert! ((hjet (i.val+2)).neg.pow (l i)).div_const (c:=((l i).factorial:ℝ)) using 1
    · exact haa.pow _
    · exact pow_ne_zero _ ha
  · have hf : (fun y => shifted P g d y / externalOddWeight d) = fun _ => 0 := by
      funext y
      simp [shifted,hv]
    rw [hf]
    exact analyticAt_const
end WP
