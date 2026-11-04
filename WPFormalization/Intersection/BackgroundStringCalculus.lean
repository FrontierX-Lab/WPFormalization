import WPFormalization.Intersection.BackgroundMerging
/-! Finite background differentiation without division by a background time.
Zero times and zero multiplicities are retained throughout the product rule. -/
noncomputable section
namespace WP
lemma sum_background_delete {N B k : ℕ} (i : Fin N) (hk : k+(i.val+1)≤B)
    (F : (Fin N→ℕ)→(Fin N→ℕ)→ℝ) :
    (∑ l ∈ backgroundVectors N B (k+(i.val+1)),
      if 0<l i then F l (Function.update l i (l i-1)) else 0) =
      ∑ l ∈ backgroundVectors N B k, F (Function.update l i (l i+1)) l := by
  have hk' : k≤B := by omega
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun l _ => Function.update l i (l i+1))
  · intro l hl
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_backgroundVectors_iff N B _ hk _).mpr
      rw [background_degree_update,(mem_backgroundVectors_iff N B k hk' l).mp hl]
      simp
    · simp
  · intro l hl j hj he
    funext a
    by_cases ha : a=i
    · subst a
      have hv := congrFun he i
      simp only [Function.update_self] at hv
      omega
    · have hv := congrFun he a
      simpa [Function.update_of_ne ha] using hv
  · intro l hl
    obtain ⟨hl,hpos⟩ := Finset.mem_filter.mp hl
    let j := Function.update l i (l i-1)
    have he : Function.update j i (j i+1)=l := update_lower_raise l i hpos
    have hdeg := background_degree_update j i 1
    rw [he,(mem_backgroundVectors_iff N B _ hk l).mp hl] at hdeg
    have hj : j ∈ backgroundVectors N B k := by
      apply (mem_backgroundVectors_iff N B k hk' j).mpr
      omega
    exact ⟨j,hj,he⟩
  · intro l hl
    rw [update_raise_lower]

lemma exponential_weight_derivative (t : ℝ) (n : ℕ) :
    (n:ℝ)*t^(n-1)/(n.factorial:ℝ)=
      if 0<n then t^(n-1)/((n-1).factorial:ℝ) else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Nat.succ_pos,ite_true,
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast n.factorial_ne_zero
    field_simp

lemma background_weight_derivative_term {N : ℕ} (t : Fin N→ℝ) (l : Fin N→ℕ)
    (i : Fin N) (v : ℝ) :
    (∏ j ∈ Finset.univ.erase i, t j^(l j)/(l j).factorial)*
      ((l i:ℝ)*t i^(l i-1)*v/(l i).factorial) =
      if 0<l i then v*(∏ j : Fin N,
        t j^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0 := by
  by_cases hi : 0<l i
  · rw [if_pos hi]
    rw [←Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
    have he : (∏ j ∈ Finset.univ.erase i,
        t j^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial)=
        ∏ j ∈ Finset.univ.erase i, t j^(l j)/(l j).factorial := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [he,Function.update_self]
    have hn := exponential_weight_derivative (t i) (l i)
    rw [if_pos hi] at hn
    linear_combination (v*(∏ j ∈ Finset.univ.erase i,t j^(l j)/(l j).factorial))*hn
  · have hz : l i=0 := by omega
    simp [hi,hz]
lemma hasDerivAt_background_weight {N : ℕ} (t : Fin N→ℝ→ℝ) (v : Fin N→ℝ)
    (l : Fin N→ℕ) (Y : ℝ) (ht : ∀i,HasDerivAt (t i) (v i) Y) :
    HasDerivAt (fun x : ℝ => ∏ i : Fin N,t i x^(l i)/(l i).factorial)
      (∑ i : Fin N, if 0<l i then v i*(∏ j : Fin N,
        t j Y^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0) Y := by
  have hd := HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i hi => ((ht i).pow (l i)).div_const ((l i).factorial:ℝ))
  convert! hd using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul]
  exact (background_weight_derivative_term (fun j=>t j Y) l i (v i)).symm
lemma hasDerivAt_inverse_nat_power (f : ℝ→ℝ) (u v : ℝ) (n : ℕ)
    (hf : HasDerivAt f (-v) u) (hne : f u≠0) :
    HasDerivAt (fun x : ℝ => 1/f x^n) ((n:ℝ)*v/f u^(n+1)) u := by
  have hz := (hasDerivAt_zpow (-(n:ℤ)) (f u) (Or.inl hne)).comp u hf
  have he : -(n:ℤ)-1= -((n+1:ℕ):ℤ) := by omega
  rw [he] at hz
  simp only [Int.cast_neg,Int.cast_natCast,zpow_neg,zpow_natCast,inv_eq_one_div] at hz
  convert! hz using 1 <;> ring

lemma hasDerivAt_weighted_background_term {N : ℕ} (t : Fin N→ℝ→ℝ) (v : Fin N→ℝ)
    (l : Fin N→ℕ) (f : ℝ→ℝ) (Y w : ℝ) (n : ℕ)
    (ht : ∀i,HasDerivAt (t i) (v i) Y) (hf : HasDerivAt f (-w) Y) (hne : f Y≠0) :
    HasDerivAt (fun x : ℝ => (∏ i : Fin N,t i x^(l i)/(l i).factorial)/f x^n)
      ((∑ i : Fin N, if 0<l i then v i*(∏ j : Fin N,
        t j Y^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0)/f Y^n+
        (∏ i : Fin N,t i Y^(l i)/(l i).factorial)*((n:ℝ)*w/f Y^(n+1))) Y := by
  have hp := (hasDerivAt_background_weight t v l Y ht).mul
    (hasDerivAt_inverse_nat_power f Y w n hf hne)
  convert! hp using 1
  · ext x
    simp only [Pi.mul_apply]
    ring
  · ring
end WP
