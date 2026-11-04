import WPFormalization.Intersection.ShiftedStringRegularity
/-! The genuine degree-zero shifted string flow in the parameter Y.
The proof differentiates the original finite background sum, aggregates the
classical string law with exact multiplicities, and uses dilaton for the
denominator derivative. Background times are never divided out. -/
noncomputable section
namespace WP
def zeroRawAmplitude (P : PsiTheory) (g p N B M : ℕ) (a : ℝ) (t : Fin N→ℝ) : ℝ :=
  ∑ l ∈ backgroundVectors N B M,
    P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
      (∏ i,t i^(l i)/(l i).factorial)/a^(complexity g p+∑i,l i)
lemma shifted_zero_diagonal_background (P : PsiTheory) (g p : ℕ) (hs : Stable g p) (Y : ℝ) :
    shifted P g (List.replicate p 0) Y =
      zeroRawAmplitude P g p (dimension g p) (dimension g p) (dimension g p) (a Y)
        (fun i : Fin (dimension g p)=>-(iteratedDeriv (i.val+2) X Y).re) := by
  have hdef : deficit g (List.replicate p 0)=dimension g p := by simp [deficit]
  have hvalid : Stable g (List.replicate p 0).length ∧
      (List.replicate p 0).sum   ≤   dimension g (List.replicate p 0).length := by simpa using hs
  rw [←hdef]
  unfold shifted zeroRawAmplitude
  rw [if_pos hvalid]
  simp only [List.length_replicate,List.map_replicate,List.prod_replicate]
  have ho : oddFactorial 0=1 := by simp [oddFactorial]
  rw [ho]
  simp only [Nat.cast_one,one_pow,one_mul,backgroundVectors_diagonal]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [pure,List.map_append,List.map_replicate,Int.ofNat_eq_natCast,Nat.cast_zero]
lemma zeroRawAmplitude_string (P : PsiTheory) (g p N B M : ℕ) (hs : Stable g p)
    (a : ℝ) (ha : a≠0) (t : Fin N→ℝ) :
    a*zeroRawAmplitude P g (p+1) N B M a t =
      ∑ l ∈ backgroundVectors N B M, ∑ i : Fin N,
        (l i:ℝ)*(∏j,t j^(l j)/(l j).factorial)*
          P.psi g (((i.val+1:ℕ):ℤ)::List.replicate p 0 ++
            (backgroundDegrees (Function.update l i (l i-1))).map Int.ofNat)/
              a^(complexity g p+∑j,l j) := by
  have hc : complexity g (p+1)=complexity g p+1 := by unfold complexity Stable at *;omega
  unfold zeroRawAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [psi_zeros_background_string P g p hs l,hc,Finset.sum_mul,Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show complexity g p+1+(∑j,l j)=(complexity g p+∑j,l j)+1 by omega,pow_succ]
  field_simp
  <;>ring

def zeroInsertionSum (P : PsiTheory) (g p N B k h mark : ℕ) (a : ℝ) (t : Fin N→ℝ) : ℝ :=
  ∑ l ∈ backgroundVectors N B k,
    (∏j,t j^(l j)/(l j).factorial)*
      P.psi g ((mark:ℤ)::List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)/
        a^(h+∑j,l j+1)
lemma zeroRawAmplitude_string_operator (P : PsiTheory) (g p N B M : ℕ)
    (hs : Stable g p) (hM : M   ≤   B) (a : ℝ) (ha : a≠0) (t : Fin N→ℝ) :
    a*zeroRawAmplitude P g (p+1) N B M a t =
      ∑ i : Fin N, if i.val+1   ≤   M then
        t i*zeroInsertionSum P g p N B (M-(i.val+1)) (complexity g p) (i.val+1) a t else 0 := by
  rw [zeroRawAmplitude_string P g p N B M hs a ha t,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : i.val+1   ≤   M
  · rw [if_pos hb]
    have he := background_raising_denominator P g (((i.val+1:ℕ):ℤ)::List.replicate p 0)
      i (k:=M-(i.val+1)) (B:=B) (by omega) (complexity g p) a t
    rw [Nat.sub_add_cancel hb] at he
    simpa only [zeroInsertionSum,List.cons_append] using he
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro l hl
    have hz := background_zero_of_ge hM l hl i (by omega)
    simp [hz]

def zeroTimeDerivative (P : PsiTheory) (g p N B M : ℕ) (a : ℝ) (t v : Fin N→ℝ) : ℝ :=
  ∑ l ∈ backgroundVectors N B M,
    P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
      (∑ i : Fin N, if 0<l i then v i*(∏j : Fin N,
        t j^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0)/
          a^(complexity g p+∑j,l j)
lemma zeroTimeDerivative_operator (P : PsiTheory) (g p N B M : ℕ) (hM : M   ≤   B)
    (a : ℝ) (t v : Fin N→ℝ) :
    zeroTimeDerivative P g p N B M a t v =
      ∑ i : Fin N, if i.val+1   ≤   M then
        v i*zeroInsertionSum P g p N B (M-(i.val+1)) (complexity g p) (i.val+2) a t else 0 := by
  unfold zeroTimeDerivative
  simp_rw [Finset.mul_sum,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : i.val+1   ≤   M
  · rw [if_pos hb]
    let F := fun l j : Fin N→ℕ =>
      P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*v i*
        (∏k,t k^(j k)/(j k).factorial)/a^(complexity g p+∑k,l k)
    have he := sum_background_delete i (k:=M-(i.val+1)) (B:=B) (by omega) F
    rw [Nat.sub_add_cancel hb] at he
    have heq : (∑ l ∈ backgroundVectors N B M,
        P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
          (if 0<l i then v i*(∏j : Fin N,
            t j^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0)/
              a^(complexity g p+∑j,l j))=
        ∑ l ∈ backgroundVectors N B M,if 0<l i then F l (Function.update l i (l i-1)) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> simp only [F,mul_zero,zero_div] <;> ring
    rw [heq,he]
    unfold zeroInsertionSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    dsimp only [F]
    rw [background_size_update]
    have hp := psi_background_raise P g (List.replicate p 0)
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

lemma zeroRawAmplitude_string_time (P : PsiTheory) (g p m : ℕ) (hs : Stable g p)
    (a : ℝ) (ha : a≠0) (t : ℕ→ℝ) :
    a*zeroRawAmplitude P g (p+1) (m+1) (m+1) (m+1) a (fun i=>t i.val)=
      t 0*zeroInsertionSum P g p (m+1) (m+1) m (complexity g p) 1 a (fun i=>t i.val)+
      zeroTimeDerivative P g p (m+1) (m+1) m a (fun i=>t i.val) (fun i=>t (i.val+1)) := by
  have hL := zeroRawAmplitude_string_operator P g p (m+1) (m+1) (m+1) hs
    (by omega) a ha (fun i=>t i.val)
  have hR := zeroTimeDerivative_operator P g p (m+1) (m+1) m (by omega)
    a (fun i=>t i.val) (fun i=>t (i.val+1))
  rw [Fin.sum_univ_succ] at hL
  rw [Fin.sum_univ_castSucc] at hR
  simp only [Fin.val_zero,Fin.val_succ,zero_add,show 1  ≤  m+1 by omega,ite_true,
    Nat.add_sub_cancel] at hL
  simp only [Fin.val_castSucc,Fin.val_last,show ¬m+1  ≤  m by omega,ite_false,add_zero] at hR
  rw [hL,hR]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hb : i.val+1  ≤  m := by omega
  have hb' : i.val+1+1  ≤  m+1 := by omega
  rw [if_pos hb,if_pos hb']
  congr 2
  omega

lemma zeroDerivative_sum_eq_child (P : PsiTheory) (g p m : ℕ) (hs : Stable g p)
    (a : ℝ) (ha : a≠0) (t : ℕ→ℝ) :
    (∑ l ∈ backgroundVectors (m+1) (m+1) m,
      P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
        backgroundRationalDerivative (fun i : Fin (m+1)=>t i.val) (fun i=>t (i.val+1))
          l a (t 0) (complexity g p+∑i,l i)) =
      a*zeroRawAmplitude P g (p+1) (m+1) (m+1) (m+1) a (fun i=>t i.val) := by
  have hscale : t 0*zeroInsertionSum P g p (m+1) (m+1) m (complexity g p) 1 a (fun i=>t i.val)=
      ∑ l ∈ backgroundVectors (m+1) (m+1) m,
        P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
          (∏i : Fin (m+1),t i.val^(l i)/(l i).factorial)*
            (((complexity g p+∑i,l i:ℕ):ℝ)*t 0/a^(complexity g p+∑i,l i+1)) := by
    unfold zeroInsertionSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    norm_num only [Nat.cast_one]
    rw [psi_one_zero_background P g p hs l]
    simp only [Nat.cast_add]
    ring
  calc _ = zeroTimeDerivative P g p (m+1) (m+1) m a (fun i=>t i.val) (fun i=>t (i.val+1))+
          t 0*zeroInsertionSum P g p (m+1) (m+1) m (complexity g p) 1 a (fun i=>t i.val) := by
          rw [hscale,zeroTimeDerivative,←Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro l hl
          unfold backgroundRationalDerivative
          ring
       _ = _ := by rw [zeroRawAmplitude_string_time P g p m hs a ha t];ring

lemma shifted_zero_hasDerivAt (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (ha : a Y≠0) :
    HasDerivAt (fun t : ℝ => shifted P g (List.replicate p 0) t)
      (a Y*shifted P g (List.replicate (p+1) 0) Y) Y := by
  have hd := shifted_zero_hasDerivAt_finite P g p hs Y ha
  have hs' : Stable g (p+1) := by unfold Stable at *;omega
  have hm : dimension g (p+1)=dimension g p+1 := by unfold dimension Stable at *;omega
  have hc := shifted_zero_diagonal_background P g (p+1) hs' Y
  rw [hm] at hc
  have he := zeroDerivative_sum_eq_child P g p (dimension g p) hs (a Y) ha
    (fun n : ℕ=>-(iteratedDeriv (n+2) X Y).re)
  simp only [Nat.zero_add,show ∀n : ℕ,n+1+2=n+3 by intro n;omega] at he
  rw [←hc] at he
  rw [he] at hd
  exact hd
end WP
