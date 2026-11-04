import WPFormalization.Intersection.ShiftedStringDerivative
noncomputable section
namespace WP
lemma psi_marked_background_string (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hs : Stable g d.length) {N : ℕ} (l : Fin N → ℕ) :
    P.psi g (0::d ++ (backgroundDegrees l).map Int.ofNat) =
      (∑ j ∈ Finset.range d.length,
        P.psi g (d.set j (d[j]!-1) ++ (backgroundDegrees l).map Int.ofNat)) +
      ∑ i : Fin N, (l i:ℝ)*P.psi g (((i.val+1:ℕ):ℤ) :: d ++
        (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) := by
  let e := d ++ (backgroundDegrees l).map Int.ofNat
  have hstable : Stable g e.length := by
    simp only [e,List.length_append,List.length_map]
    unfold Stable at *
    omega
  have he := P.string g e hstable
  have hlen : e.length = d.length+(backgroundDegrees l).length := by simp [e]
  rw [hlen,Finset.sum_range_add] at he
  change P.psi g (0::e) = _
  rw [he,← sum_background_lowerings P g d l]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hget : e[j]! = d[j]! := by
      apply List.getElem!_of_getElem?
      change (d ++ (backgroundDegrees l).map Int.ofNat)[j]? = some d[j]!
      rw [List.getElem?_append_left hj']
      simp [hj']
    rw [hget]
    congr 1
    simp [e,List.set_append, hj']
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hidx : d.length+j<e.length := by omega
    have hget : e[d.length+j]! = (((backgroundDegrees l)[j]!:ℕ):ℤ) := by
      apply List.getElem!_of_getElem?
      change (d ++ (backgroundDegrees l).map Int.ofNat)[d.length+j]? = _
      rw [List.getElem?_append_right (by omega)]
      simp [List.getElem?_map,hj']
    have herase : e.eraseIdx (d.length+j) = d ++ ((backgroundDegrees l).eraseIdx j).map Int.ofNat := by
      change (d ++ (backgroundDegrees l).map Int.ofNat).eraseIdx (d.length+j) = _
      rw [List.eraseIdx_append_of_length_le (by omega)]
      simp only [Nat.add_sub_cancel_left,List.eraseIdx_map]
    rw [hget,P.symmetry g _ _ (List.set_perm_cons_eraseIdx hidx _),herase]
    simp only [List.cons_append]
end WP
namespace WP
open Set Filter
open scoped Topology

def markedRawAmplitude (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (N B M : ℕ) (a : ℝ) (t : Fin N → ℝ) : ℝ :=
    ∑ l ∈ backgroundVectors N B M,
      P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) *
      (∏ i, t i^(l i)/(l i).factorial)/a^(complexity g d.length+∑ i,l i)

lemma markedRawAmplitude_string (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (N B M : ℕ) (hs : Stable g d.length) (a : ℝ) (ha : a ≠ 0) (t : Fin N → ℝ) :
    a*markedRawAmplitude P g (0::d) N B M a t =
      (∑ j ∈ Finset.range d.length,
        markedRawAmplitude P g (d.set j (d[j]!-1)) N B M a t) +
      ∑ l ∈ backgroundVectors N B M, ∑ i : Fin N,
        (l i:ℝ)*(∏ j,t j^(l j)/(l j).factorial)*
        P.psi g (((i.val+1:ℕ):ℤ)::d ++
          (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)/
          a^(complexity g d.length+∑ j,l j) := by
  have hc : complexity g (0::d).length = complexity g d.length+1 := by
    simp only [List.length_cons]
    unfold complexity Stable at *
    omega
  have he : a*markedRawAmplitude P g (0::d) N B M a t =
      ∑ l ∈ backgroundVectors N B M,
        ((∑ j ∈ Finset.range d.length,
          P.psi g (d.set j (d[j]!-1) ++ (backgroundDegrees l).map Int.ofNat)) +
        ∑ i : Fin N, (l i:ℝ)*P.psi g (((i.val+1:ℕ):ℤ)::d ++
          (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat))*
        (∏ j,t j^(l j)/(l j).factorial)/a^(complexity g d.length+∑ j,l j) := by
    unfold markedRawAmplitude
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← psi_marked_background_string P g d hs l,hc,
      show complexity g d.length+1+(∑ j,l j) = (complexity g d.length+∑ j,l j)+1 by omega,pow_succ]
    field_simp
    <;> ring
  rw [he]
  simp_rw [add_mul,add_div,Finset.sum_mul,Finset.sum_div]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [markedRawAmplitude,List.length_set]
  · apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro i hi
    ring
end WP

namespace WP
def markedInsertionSum (P : PsiTheory) (g : ℕ) (d : List ℤ) (N B k h mark : ℕ) (a : ℝ) (t : Fin N→ℝ) : ℝ :=
  ∑ l ∈ backgroundVectors N B k,
    (∏j,t j^(l j)/(l j).factorial)*
      P.psi g ((mark:ℤ)::d ++ (backgroundDegrees l).map Int.ofNat)/
        a^(h+∑j,l j+1)
def markedTimeDerivative (P : PsiTheory) (g : ℕ) (d : List ℤ) (N B M : ℕ) (a : ℝ) (t v : Fin N→ℝ) : ℝ :=
  ∑ l ∈ backgroundVectors N B M,
    P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
      (∑ i : Fin N, if 0<l i then v i*(∏j : Fin N,
        t j^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0)/
          a^(complexity g d.length+∑j,l j)
lemma markedTimeDerivative_operator (P : PsiTheory) (g : ℕ) (d : List ℤ) (N B M : ℕ) (hM : M   ≤   B)
    (a : ℝ) (t v : Fin N→ℝ) :
    markedTimeDerivative P g d N B M a t v =
      ∑ i : Fin N, if i.val+1   ≤   M then
        v i*markedInsertionSum P g d N B (M-(i.val+1)) (complexity g d.length) (i.val+2) a t else 0 := by
  unfold markedTimeDerivative
  simp_rw [Finset.mul_sum,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : i.val+1   ≤   M
  · rw [if_pos hb]
    let F := fun l j : Fin N→ℕ =>
      P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*v i*
        (∏k,t k^(j k)/(j k).factorial)/a^(complexity g d.length+∑k,l k)
    have he := sum_background_delete i (k:=M-(i.val+1)) (B:=B) (by omega) F
    rw [Nat.sub_add_cancel hb] at he
    have heq : (∑ l ∈ backgroundVectors N B M,
        P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
          (if 0<l i then v i*(∏j : Fin N,
            t j^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0)/
              a^(complexity g d.length+∑j,l j))=
        ∑ l ∈ backgroundVectors N B M,if 0<l i then F l (Function.update l i (l i-1)) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> simp only [F,mul_zero,zero_div] <;> ring
    rw [heq,he]
    unfold markedInsertionSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    dsimp only [F]
    rw [background_size_update]
    have hp := psi_background_raise P g (d)
      (Function.update l i (l i+1)) i (by simp)
    rw [update_raise_lower] at hp
    rw [←hp]
    simp only [List.cons_append,Nat.add_assoc]
    ring
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro l hl
    have hz := background_zero_of_ge hM l hl i (by omega)
    simp [hz]

end WP
namespace WP
lemma markedRawAmplitude_string_operator (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (N B M : ℕ) (hs : Stable g d.length) (hM : M ≤ B)
    (a : ℝ) (ha : a ≠ 0) (t : Fin N → ℝ) :
    a*markedRawAmplitude P g (0::d) N B M a t =
      (∑ j ∈ Finset.range d.length, markedRawAmplitude P g (d.set j (d[j]!-1)) N B M a t) +
      ∑ i : Fin N, if i.val+1 ≤ M then
        t i*markedInsertionSum P g d N B (M-(i.val+1)) (complexity g d.length) (i.val+1) a t else 0 := by
  rw [markedRawAmplitude_string P g d N B M hs a ha t]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : i.val+1 ≤ M
  · rw [if_pos hb]
    have he := background_raising_denominator P g (((i.val+1:ℕ):ℤ)::d)
      i (k:=M-(i.val+1)) (B:=B) (by omega) (complexity g d.length) a t
    rw [Nat.sub_add_cancel hb] at he
    simpa only [markedInsertionSum,List.cons_append] using he
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro l hl
    have hz := background_zero_of_ge hM l hl i (by omega)
    simp [hz]

lemma markedRawAmplitude_string_time (P : PsiTheory) (g : ℕ) (d : List ℤ) (m : ℕ)
    (hs : Stable g d.length) (a : ℝ) (ha : a ≠ 0) (t : ℕ → ℝ) :
    a*markedRawAmplitude P g (0::d) (m+1) (m+1) (m+1) a (fun i=>t i.val) =
      (∑ j ∈ Finset.range d.length,
        markedRawAmplitude P g (d.set j (d[j]!-1)) (m+1) (m+1) (m+1) a (fun i=>t i.val)) +
      (t 0*markedInsertionSum P g d (m+1) (m+1) m (complexity g d.length) 1 a (fun i=>t i.val) +
      markedTimeDerivative P g d (m+1) (m+1) m a (fun i=>t i.val) (fun i=>t (i.val+1))) := by
  have hL := markedRawAmplitude_string_operator P g d (m+1) (m+1) (m+1) hs
    (by omega) a ha (fun i=>t i.val)
  have hR := markedTimeDerivative_operator P g d (m+1) (m+1) m (by omega)
    a (fun i=>t i.val) (fun i=>t (i.val+1))
  rw [Fin.sum_univ_succ] at hL
  rw [Fin.sum_univ_castSucc] at hR
  simp only [Fin.val_zero,Fin.val_succ,zero_add,show 1 ≤ m+1 by omega,ite_true,
    Nat.add_sub_cancel] at hL
  simp only [Fin.val_castSucc,Fin.val_last,show ¬m+1 ≤ m by omega,ite_false,add_zero] at hR
  rw [hL,hR]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hb : i.val+1 ≤ m := by omega
  have hb' : i.val+1+1 ≤ m+1 := by omega
  rw [if_pos hb,if_pos hb']
  congr 2
  omega

lemma psi_one_marked_background (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hs : Stable g d.length) {N : ℕ} (l : Fin N → ℕ) :
    P.psi g (1::d ++ (backgroundDegrees l).map Int.ofNat) =
      ((complexity g d.length:ℝ)+(∑ i,l i:ℕ))*P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) := by
  have hstable : Stable g (d ++ (backgroundDegrees l).map Int.ofNat).length := by
    simp only [List.length_append,List.length_map]
    unfold Stable at *
    omega
  simp only [List.cons_append]
  rw [P.dilaton g _ hstable]
  simp only [List.length_append,List.length_map,backgroundDegrees_length,Nat.cast_add]
  have hc : (complexity g d.length:ℝ) = 2*(g:ℝ)+d.length-2 := by
    unfold complexity
    rw [Nat.cast_sub (by unfold Stable at hs;omega)]
    push_cast
    ring
  rw [hc]
  ring

lemma markedDerivative_sum_eq_string (P : PsiTheory) (g : ℕ) (d : List ℤ) (m : ℕ)
    (hs : Stable g d.length) (a : ℝ) (ha : a ≠ 0) (t : ℕ → ℝ) :
    (∑ l ∈ backgroundVectors (m+1) (m+1) m,
      P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
        backgroundRationalDerivative (fun i : Fin (m+1)=>t i.val) (fun i=>t (i.val+1))
          l a (t 0) (complexity g d.length+∑ i,l i)) =
      a*markedRawAmplitude P g (0::d) (m+1) (m+1) (m+1) a (fun i=>t i.val) -
        ∑ j ∈ Finset.range d.length,
          markedRawAmplitude P g (d.set j (d[j]!-1)) (m+1) (m+1) (m+1) a (fun i=>t i.val) := by
  have hscale : t 0*markedInsertionSum P g d (m+1) (m+1) m (complexity g d.length) 1 a (fun i=>t i.val) =
      ∑ l ∈ backgroundVectors (m+1) (m+1) m,
        P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
          (∏ i : Fin (m+1),t i.val^(l i)/(l i).factorial)*
          (((complexity g d.length+∑ i,l i:ℕ):ℝ)*t 0/a^(complexity g d.length+∑ i,l i+1)) := by
    unfold markedInsertionSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    norm_num only [Nat.cast_one]
    rw [psi_one_marked_background P g d hs l]
    simp only [Nat.cast_add]
    ring
  have he : (∑ l ∈ backgroundVectors (m+1) (m+1) m,
      P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
        backgroundRationalDerivative (fun i : Fin (m+1)=>t i.val) (fun i=>t (i.val+1))
          l a (t 0) (complexity g d.length+∑ i,l i)) =
      markedTimeDerivative P g d (m+1) (m+1) m a (fun i=>t i.val) (fun i=>t (i.val+1)) +
      t 0*markedInsertionSum P g d (m+1) (m+1) m (complexity g d.length) 1 a (fun i=>t i.val) := by
    rw [hscale,markedTimeDerivative,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    unfold backgroundRationalDerivative
    ring
  rw [he,markedRawAmplitude_string_time P g d m hs a ha t]
  ring
end WP
namespace WP
lemma markedRawAmplitude_parameter_hasDerivAt (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (m : ℕ) (hs : Stable g d.length) (Y : ℝ) (ha : a Y ≠ 0) :
    HasDerivAt (fun y : ℝ => markedRawAmplitude P g d (m+1) (m+1) m (a y)
      (fun i => -(iteratedDeriv (i.val+2) X y).re))
      (a Y*markedRawAmplitude P g (0::d) (m+1) (m+1) (m+1) (a Y)
        (fun i => -(iteratedDeriv (i.val+2) X Y).re) -
        ∑ j ∈ Finset.range d.length,
          markedRawAmplitude P g (d.set j (d[j]!-1)) (m+1) (m+1) (m+1) (a Y)
            (fun i => -(iteratedDeriv (i.val+2) X Y).re)) Y := by
  have hd : HasDerivAt (fun y : ℝ => markedRawAmplitude P g d (m+1) (m+1) m (a y)
      (fun i => -(iteratedDeriv (i.val+2) X y).re))
      (∑ l ∈ backgroundVectors (m+1) (m+1) m,
        P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)*
          backgroundRationalDerivative
            (fun i : Fin (m+1) => -(iteratedDeriv (i.val+2) X Y).re)
            (fun i => -(iteratedDeriv (i.val+3) X Y).re)
            l (a Y) (-(iteratedDeriv 2 X Y).re) (complexity g d.length+∑ i,l i)) Y := by
    unfold markedRawAmplitude
    apply HasDerivAt.fun_sum
    intro l hl
    have ht := (hasDerivAt_weighted_background_term
      (fun i : Fin (m+1) => fun y : ℝ => -(iteratedDeriv (i.val+2) X y).re)
      (fun i : Fin (m+1) => -(iteratedDeriv (i.val+3) X Y).re)
      l a Y (-(iteratedDeriv 2 X Y).re) (complexity g d.length+∑ i,l i)
      (fun i => hasDerivAt_background_time i.val Y)
      (by simpa only [neg_neg] using a_hasDerivAt Y) ha).const_mul
        (P.psi g (d ++ (backgroundDegrees l).map Int.ofNat))
    convert ht using 1
    · ext y
      ring
    · rfl
  have he := markedDerivative_sum_eq_string P g d m hs (a Y) ha
    (fun n : ℕ => -(iteratedDeriv (n+2) X Y).re)
  simp only [Nat.zero_add,show ∀ n : ℕ,n+1+2=n+3 by intro n;omega] at he
  rw [he] at hd
  exact hd
end WP
namespace WP

def externalOddWeight (d : List ℕ) : ℝ := (d.map (fun k => (oddFactorial k:ℝ))).prod
lemma externalOddWeight_ne_zero (d : List ℕ) : externalOddWeight d ≠ 0 := by
  unfold externalOddWeight
  apply List.prod_ne_zero
  intro hx
  obtain ⟨k,hk,hzero⟩ := List.mem_map.mp hx
  exact (show (oddFactorial k:ℝ) ≠ 0 by exact_mod_cast oddFactorial_ne_zero k) hzero

lemma shifted_div_odd_eq_markedRaw_diagonal (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length) (Y : ℝ) :
    shifted P g d Y / externalOddWeight d =
      markedRawAmplitude P g (d.map Int.ofNat) (deficit g d) (deficit g d) (deficit g d) (a Y)
        (fun i => -(iteratedDeriv (i.val+2) X Y).re) := by
  unfold shifted
  rw [if_pos ⟨hs,hd⟩]
  rw [show (d.map (fun k => (oddFactorial k:ℝ))).prod = externalOddWeight d from rfl,
    mul_div_cancel_left₀ _ (externalOddWeight_ne_zero d)]
  simp only [markedRawAmplitude,backgroundVectors_diagonal,List.length_map,pure,List.map_append]

lemma shifted_div_odd_eq_markedRaw_fixed (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length) (Y : ℝ) :
    shifted P g d Y / externalOddWeight d =
      markedRawAmplitude P g (d.map Int.ofNat) (deficit g d+1) (deficit g d+1) (deficit g d) (a Y)
        (fun i => -(iteratedDeriv (i.val+2) X Y).re) := by
  rw [shifted_div_odd_eq_markedRaw_diagonal P g d hs hd]
  unfold markedRawAmplitude
  rw [sum_backgroundVectors_zeroExtend (deficit g d) 1 (deficit g d+1) (by omega)]
  simp only [backgroundVectors_diagonal,List.length_map]
  apply Finset.sum_congr rfl
  intro l hl
  rw [backgroundDegrees_zeroExtend,background_weight_zeroExtend]
  have hsize : (∑ i : Fin (deficit g d+1), zeroExtendBackground 1 l i) = ∑ i : Fin (deficit g d), l i := by
    rw [←backgroundDegrees_length,backgroundDegrees_zeroExtend,backgroundDegrees_length]
  rw [hsize]
  rfl

lemma markedRawAmplitude_negative (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (N B M : ℕ) (a : ℝ) (t : Fin N → ℝ) (hd : ∃ k ∈ d, k < 0) :
    markedRawAmplitude P g d N B M a t = 0 := by
  unfold markedRawAmplitude
  apply Finset.sum_eq_zero
  intro l hl
  have hz : P.psi g (d ++ (backgroundDegrees l).map Int.ofNat) = 0 := by
    apply psi_negative_entry
    obtain ⟨k,hk,hneg⟩ := hd
    exact ⟨k,List.mem_append_left _ hk,hneg⟩
  rw [hz,zero_mul,zero_div]

lemma markedRawAmplitude_external_lowering_zero (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (j : ℕ) (hj : j < d.length) (hz : d[j]! = 0)
    (N B M : ℕ) (a : ℝ) (t : Fin N → ℝ) :
    markedRawAmplitude P g ((d.map Int.ofNat).set j ((d.map Int.ofNat)[j]!-1)) N B M a t = 0 := by
  have hget : (d.map Int.ofNat)[j]! = 0 := by
    have hz' : d[j] = 0 := by simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hz
    simp [hj,hz']
  rw [hget]
  norm_num only [zero_sub]
  apply markedRawAmplitude_negative
  exact ⟨-1,List.mem_set (by simpa only [List.length_map] using hj) _,by norm_num⟩

lemma lower_entry_sum (d : List ℕ) (j : ℕ) (hj : j < d.length) (hpos : 0 < d[j]!) :
    (d.set j (d[j]!-1)).sum+1=d.sum := by
  have h1 := (List.set_perm_cons_eraseIdx hj (d[j]!-1)).sum_eq
  have h2 := (List.getElem_cons_eraseIdx_perm hj).sum_eq
  simp only [List.sum_cons] at h1 h2
  have hget : d[j] = d[j]! := by simp [hj]
  rw [hget] at h2
  omega

lemma markedRawAmplitude_external_lowering_pos (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length)
    (j : ℕ) (hj : j < d.length) (hpos : 0 < d[j]!) (Y : ℝ) :
    markedRawAmplitude P g ((d.map Int.ofNat).set j ((d.map Int.ofNat)[j]!-1))
      (deficit g d+1) (deficit g d+1) (deficit g d+1) (a Y)
      (fun i => -(iteratedDeriv (i.val+2) X Y).re) =
    shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) := by
  have hsum := lower_entry_sum d j hj hpos
  have hvalid : (d.set j (d[j]!-1)).sum ≤ dimension g (d.set j (d[j]!-1)).length := by
    simp only [List.length_set]
    omega
  have hdef : deficit g (d.set j (d[j]!-1)) = deficit g d+1 := by
    unfold deficit
    simp only [List.length_set]
    omega
  have he := shifted_div_odd_eq_markedRaw_diagonal P g (d.set j (d[j]!-1))
    (by simpa only [List.length_set] using hs) hvalid Y
  rw [hdef] at he
  have hlist : (d.map Int.ofNat).set j ((d.map Int.ofNat)[j]!-1) =
      (d.set j (d[j]!-1)).map Int.ofNat := by
    rw [List.map_set]
    have hget : (d.map Int.ofNat)[j]! = (d[j]!:ℤ) := by simp [hj]
    rw [hget]
    have hcast : ((d[j]! - 1 : ℕ) : ℤ) = (d[j]! : ℤ) - 1 := by omega
    simpa only [Int.ofNat_eq_natCast] using congrArg ((d.map Int.ofNat).set j) hcast.symm
  rw [hlist]
  exact he.symm
end WP
namespace WP
lemma shifted_unweighted_marked_hasDerivAt (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length) (Y : ℝ) (ha : a Y ≠ 0) :
    HasDerivAt (fun y : ℝ => shifted P g d y / externalOddWeight d)
      (a Y*(shifted P g (0::d) Y / externalOddWeight (0::d)) -
        ∑ j ∈ Finset.range d.length, if 0 < d[j]! then
          shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) else 0) Y := by
  have hfun : (fun y : ℝ => shifted P g d y / externalOddWeight d) =
      fun y : ℝ => markedRawAmplitude P g (d.map Int.ofNat)
        (deficit g d+1) (deficit g d+1) (deficit g d) (a y)
        (fun i => -(iteratedDeriv (i.val+2) X y).re) :=
    funext (shifted_div_odd_eq_markedRaw_fixed P g d hs hd)
  rw [hfun]
  have hder := markedRawAmplitude_parameter_hasDerivAt P g (d.map Int.ofNat) (deficit g d)
    (by simpa only [List.length_map] using hs) Y ha
  have hs0 : Stable g (0::d).length := by simp only [List.length_cons];unfold Stable at *;omega
  have hd0 : (0::d).sum ≤ dimension g (0::d).length := by
    simp only [List.sum_cons,List.length_cons,zero_add]
    unfold dimension at *
    unfold Stable at hs
    omega
  have hm0 : deficit g (0::d) = deficit g d+1 := by
    unfold deficit dimension
    simp only [List.sum_cons,List.length_cons,zero_add]
    unfold Stable at hs
    unfold dimension at hd
    omega
  have he0 := (shifted_div_odd_eq_markedRaw_diagonal P g (0::d) hs0 hd0 Y).symm
  rw [hm0] at he0
  simp only [List.map_cons,Int.ofNat_eq_natCast,Nat.cast_zero] at he0
  rw [he0] at hder
  have helow : (∑ j ∈ Finset.range (d.map Int.ofNat).length,
      markedRawAmplitude P g ((d.map Int.ofNat).set j ((d.map Int.ofNat)[j]!-1))
        (deficit g d+1) (deficit g d+1) (deficit g d+1) (a Y)
        (fun i => -(iteratedDeriv (i.val+2) X Y).re)) =
      ∑ j ∈ Finset.range d.length, if 0 < d[j]! then
        shifted P g (d.set j (d[j]!-1)) Y / externalOddWeight (d.set j (d[j]!-1)) else 0 := by
    simp only [List.length_map]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    split_ifs with hjpos
    · exact markedRawAmplitude_external_lowering_pos P g d hs hd j hj' hjpos Y
    · exact markedRawAmplitude_external_lowering_zero P g d j hj' (by omega) _ _ _ _ _
  rw [helow] at hder
  exact hder
end WP
