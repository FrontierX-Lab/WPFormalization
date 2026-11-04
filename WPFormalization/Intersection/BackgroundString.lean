import WPFormalization.HigherOrder.ShiftedDilaton
import WPFormalization.Intersection.Finite
import WPFormalization.Intersection.BackgroundMerging
/-! The exact classical string identity for background multiplicities, with
negative marked entries and repeated background insertions counted explicitly. -/
noncomputable section
namespace WP
lemma sum_background_lowerings (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (l : Fin N → ℕ) :
    (∑ j ∈ Finset.range (backgroundDegrees l).length,
      P.psi g (((((backgroundDegrees l)[j]! : ℕ):ℤ)-1) :: d ++
        ((backgroundDegrees l).eraseIdx j).map Int.ofNat)) =
    ∑ i : Fin N, (l i:ℝ)*P.psi g (((i.val+1:ℕ):ℤ) :: d ++
      (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) := by
  let G : ℕ→ℝ := fun k => if h : k-2<N then
    P.psi g (((k:ℤ)-1) :: d ++
      (backgroundDegrees (Function.update l ⟨k-2,h⟩ (l ⟨k-2,h⟩-1))).map Int.ofNat) else 0
  have hG (i : Fin N) : G (i.val+2)=P.psi g (((i.val+1:ℕ):ℤ) :: d ++
      (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) := by
    simp [G,i.isLt]
    congr 2
    ring
  calc _ = ∑ j ∈ Finset.range (backgroundDegrees l).length, G (backgroundDegrees l)[j]! := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj' := Finset.mem_range.mp hj
          have hmem : (backgroundDegrees l)[j]! ∈ backgroundDegrees l := by
            simpa [hj'] using (List.getElem_mem (l:=backgroundDegrees l) j hj')
          obtain ⟨i,hli,hi⟩ := (mem_backgroundDegrees l _).mp hmem
          rw [hi,hG i]
          have hk : (((i.val+2:ℕ):ℤ)-1)=((i.val+1:ℕ):ℤ) := by omega
          rw [hk]
          apply P.symmetry
          exact (List.Perm.refl (((i.val+1:ℕ):ℤ)::d)).append
            ((background_erase_perm l j hj' i hi (Nat.pos_of_ne_zero hli)).map Int.ofNat)
       _ = ((backgroundDegrees l).map G).sum := sum_range_getElem _ G
       _ = ∑ i : Fin N, (l i:ℝ)*G (i.val+2) := sum_map_background l G
       _ = _ := by simp only [hG]

lemma psi_zeros_background_string (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    {N : ℕ} (l : Fin N → ℕ) :
    P.psi g (List.replicate (p+1) 0 ++ (backgroundDegrees l).map Int.ofNat) =
      ∑ i : Fin N, (l i:ℝ)*P.psi g (((i.val+1:ℕ):ℤ) :: List.replicate p 0 ++
        (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat) := by
  let d : List ℤ := List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat
  have hlen : d.length=p+(backgroundDegrees l).length := by simp [d]
  have hstable : Stable g d.length := by unfold Stable at *;omega
  have hstr := P.string g d hstable
  have hleft : 0::d=List.replicate (p+1) 0 ++ (backgroundDegrees l).map Int.ofNat := by
    simp [d,List.replicate_succ]
  rw [hleft,hlen,Finset.sum_range_add] at hstr
  have hz : (∑ j ∈ Finset.range p, P.psi g (d.set j (d[j]!-1)))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjp := Finset.mem_range.mp hj
    have hget : d[j]! =0 := by
      apply List.getElem!_of_getElem?
      change (List.replicate p (0:ℤ) ++ (backgroundDegrees l).map Int.ofNat)[j]?=some 0
      rw [List.getElem?_append_left (by simpa using hjp)]
      simp [List.getElem?_replicate,hjp]
    rw [hget]
    norm_num
    exact psi_set_negative P g d j (by omega)
  rw [hz,zero_add] at hstr
  rw [hstr,←sum_background_lowerings P g (List.replicate p 0) l]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hidx : p+j<d.length := by omega
  have hget : d[p+j]! =(((backgroundDegrees l)[j]!:ℕ):ℤ) := by
    apply List.getElem!_of_getElem?
    change (List.replicate p (0:ℤ) ++ (backgroundDegrees l).map Int.ofNat)[p+j]?=
      some (((backgroundDegrees l)[j]!:ℕ):ℤ)
    rw [List.getElem?_append_right (by simp)]
    simp [List.getElem?_map,hj']
  have herase : d.eraseIdx (p+j)=List.replicate p 0 ++ ((backgroundDegrees l).eraseIdx j).map Int.ofNat := by
    rw [List.eraseIdx_append_of_length_le (by simp)]
    simp [d,List.eraseIdx_map]
  rw [hget,P.symmetry g _ _ (List.set_perm_cons_eraseIdx hidx _),herase]
  simp only [List.cons_append]
lemma background_size_update {N : ℕ} (l : Fin N→ℕ) (i : Fin N) :
    (∑ j,Function.update l i (l i+1) j)=(∑ j,l j)+1 := by
  have hh := (backgroundDegrees_update_perm l i).length_eq
  simp only [List.length_cons,backgroundDegrees_length] at hh
  omega
lemma background_size_lower {N : ℕ} (l : Fin N→ℕ) (i : Fin N) (hi : 0<l i) :
    (∑ j,Function.update l i (l i-1) j)+1=∑ j,l j := by
  have hh := background_size_update (Function.update l i (l i-1)) i
  rw [update_lower_raise l i hi] at hh
  omega
lemma background_raising_denominator (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N B k : ℕ} (i : Fin N) (hk : k+(i.val+1)≤B) (h : ℕ) (a : ℝ) (t : Fin N→ℝ) :
    (∑ l ∈ backgroundVectors N B (k+(i.val+1)),
      (l i:ℝ)*(∏ j,t j^(l j)/(l j).factorial)*
        P.psi g (d ++ (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)/
          a^(h+∑ j,l j)) =
    t i*∑ l ∈ backgroundVectors N B k,
      (∏ j,t j^(l j)/(l j).factorial)*P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)/
        a^(h+∑ j,l j+1) := by
  let F := fun l : Fin N→ℕ => P.psi g (d ++ (backgroundDegrees l).map Int.ofNat)/a^(h+∑j,l j+1)
  have he := sum_background_raise i hk t F
  simp only [mul_div_assoc]
  change _ = t i*∑ l ∈ backgroundVectors N B k, (∏ j,t j^(l j)/(l j).factorial)*F l
  rw [←he]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hi : 0<l i
  · have hsize := background_size_lower l i hi
    dsimp only [F]
    rw [show h+(∑ j,Function.update l i (l i-1) j)+1=h+∑j,l j by omega]
  · have hz : l i=0 := by omega
    simp [hz]
lemma psi_one_zero_background (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    {N : ℕ} (l : Fin N→ℕ) :
    P.psi g (1::List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)=
      ((complexity g p:ℝ)+(∑i,l i:ℕ))*
        P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat) := by
  have hstable : Stable g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat).length := by
    simp only [List.length_append,List.length_replicate,List.length_map]
    unfold Stable at *
    omega
  simp only [List.cons_append]
  rw [P.dilaton g _ hstable]
  simp only [List.length_append,List.length_replicate,List.length_map,backgroundDegrees_length,Nat.cast_add]
  have hc : (complexity g p:ℝ)=2*(g:ℝ)+p-2 := by
    unfold complexity
    rw [Nat.cast_sub (by unfold Stable at hs;omega)]
    push_cast
    ring
  rw [hc]
  ring
end WP
