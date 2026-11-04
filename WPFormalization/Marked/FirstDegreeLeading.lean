import WPFormalization.Analysis.KernelPolynomialTails
import WPFormalization.HigherOrder.Coherence
import WPFormalization.Comparison.ZeroPotential
import WPFormalization.Marked.GenusExtensions

/-! The exact leading adjacent coefficient of Lemma 7.2. Real kernel sums identify the discrete correction and polynomial tail moments bound the finite-cutoff error. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP
lemma positive_count_add_zeros (d : List ℕ) :
    (d.filter (fun k => 0<k)).length + zeros d = d.length := by
  induction d with
  | nil => simp [zeros]
  | cons k d ih =>
    by_cases hk : k=0
    · subst k
      simp [List.filter_cons,zeros_cons_eq]
      omega
    · have hp : 0<k := Nat.pos_of_ne_zero hk
      simp [List.filter_cons,zeros_cons_eq,hk,hp]
      omega

lemma merger_coefficient_sum (d : List ℕ) :
    (∑ j ∈ Finset.range d.length, (2*(d[j]!:ℝ)+1)) = 2*(d.sum:ℝ)+d.length := by
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  have he := sum_range_getElem d (fun k : ℕ => (k:ℝ))
  have hc : (d.map (fun k : ℕ => (k:ℝ))).sum=(d.sum:ℝ) := (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
  rw [hc] at he
  simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]

lemma zeroCountLayer_exact (t l : ℕ) (d : List ℕ) :
    zeroCountLayer t d l =
      2*((t::d).sum:ℝ)+(t::d).length-3+2*(l:ℝ)+
        (if t=0 ∧ l=0 then 2-(zeros d:ℝ) else 0) := by
  by_cases hz : t=0 ∧ l=0
  · rcases hz with ⟨rfl,rfl⟩
    unfold zeroCountLayer
    simp only [Nat.zero_add,Nat.add_zero,Nat.zero_sub,Nat.cast_zero,mul_zero,add_zero]
    have hi : (∑ j ∈ Finset.range d.length, (2*(d[j]!:ℝ)+1)*(if 1 ≤ d[j]! then 1 else 0)) =
        (∑ j ∈ Finset.range d.length, (2*(d[j]!:ℝ)+1))-
          ∑ j ∈ Finset.range d.length, if d[j]! = 0 then (1:ℝ) else 0 := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : d[j]! = 0
      · simp [h]
      · rw [if_pos (by omega : 1 ≤ d[j]!),if_neg h,mul_one,sub_zero]
    have hz' : (∑ j ∈ Finset.range d.length, if d[j]! = 0 then (1:ℝ) else 0) = (zeros d:ℝ) := by
      exact_mod_cast zero_index_sum d
    rw [hi,hz',merger_coefficient_sum]
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Nat.zero_add,Nat.cast_zero,
      and_self,ite_true]
    ring
  · have htl : 1 ≤ t+l := by omega
    have he : zeroCountLayer t d l=(∑ j ∈ Finset.range d.length, (2*(d[j]!:ℝ)+1))+2*(t+l-1:ℕ) := by
      unfold zeroCountLayer
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (by omega : 1 ≤ t+d[j]!+l),mul_one]
    rw [he,merger_coefficient_sum,if_neg hz,Nat.cast_sub htl]
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,add_zero]
    ring

lemma degreeCorrection_adjacent (Y : ℝ) (t : ℕ) (d : List ℕ) :
    degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y =
      A Y*(Theta Y*(2*((t::d).sum:ℝ)+(t::d).length-3)+2*moment₁ Y+
        (if t=0 then 2-(zeros d:ℝ) else 0)) := by
  by_cases ht : t=0
  · subst t
    have hl := (positive_count_add_zeros d).symm
    simp only [degreeCorrection,List.sum_cons,List.length_cons,List.filter_cons,Nat.lt_irrefl,
      decide_false,ite_false,show 0<0+1 by omega,decide_true,ite_true,List.length_cons]
    rw [hl]
    push_cast
    ring
  · have htp : 0<t := Nat.pos_of_ne_zero ht
    have htp' : 0<t+1 := by omega
    simp only [degreeCorrection,List.sum_cons,List.length_cons,List.filter_cons,htp,htp',
      decide_true,ite_true,if_neg ht]
    push_cast
    ring
end WP

namespace WP
lemma zeroCountLayer_hasSum (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (t : ℕ) (d : List ℕ) :
    HasSum (fun l : ℕ => weight Y l*zeroCountLayer t d l)
      (Theta Y*(2*((t::d).sum:ℝ)+(t::d).length-3)+2*moment₁ Y+
        if t=0 then 2-(zeros d:ℝ) else 0) := by
  obtain ⟨hw,hm⟩ := HigherOrder.kernel_summable_zero_one Y hY
  have hs₀ : HasSum (weight Y) (Theta Y) := hw.hasSum
  have hs₁ : HasSum (fun l : ℕ => (l:ℝ)*weight Y l) (moment₁ Y) := hm.hasSum
  let c := 2*((t::d).sum:ℝ)+(t::d).length-3
  let e := if t=0 then 2-(zeros d:ℝ) else 0
  have heq : (fun l : ℕ => weight Y l*zeroCountLayer t d l)=
      (fun l : ℕ => (c*weight Y l+2*((l:ℝ)*weight Y l))+(if l=0 then e else 0)) := by
    funext l
    rw [zeroCountLayer_exact]
    by_cases hl : l=0
    · subst l
      rw [HigherOrder.weight_zero_eq_one Y hY]
      simp only [Nat.cast_zero,mul_zero,add_zero,ite_true]
      dsimp [c,e]
      simp only [and_true]
      ring
    · simp only [hl,and_false,ite_false,add_zero]
      dsimp [c]
      ring
  rw [heq]
  have hs := ((hs₀.mul_left c).add (hs₁.mul_left 2)).add (hasSum_ite_eq 0 e)
  convert hs using 1
  dsimp [c,e]
  ring

lemma degreeCorrection_adjacent_hasSum (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀)
    (t : ℕ) (d : List ℕ) (h : ℝ) :
    HasSum (fun l : ℕ => (A Y/h)*(weight Y l*zeroCountLayer t d l))
      ((degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h) := by
  have hs := ((zeroCountLayer_hasSum Y hY t d).mul_left (A Y)).div_const h
  rw [degreeCorrection_adjacent]
  convert hs using 1
  ext l
  ring
end WP
namespace WP
lemma zeroCountLayer_polynomial_bound (t l : ℕ) (d : List ℕ) :
    zeroCountLayer t d l ≤ ((d.length:ℝ)+5)*(((t::d).sum:ℝ)+l+1) := by
  have hm : (∑ j ∈ Finset.range d.length, (2*(d[j]!:ℝ)+1)*(if 1 ≤ t+d[j]!+l then 1 else 0)) ≤
      2*(d.sum:ℝ)+d.length := by
    rw [←merger_coefficient_sum]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · simp
    · simpa using (show (0:ℝ)≤2*(d[j]!:ℝ)+1 by positivity)
  have hp : ((t+l-1:ℕ):ℝ) ≤ (t:ℝ)+l := by exact_mod_cast (Nat.sub_le (t+l) 1)
  have hd0 : (0:ℝ)≤d.length := Nat.cast_nonneg _
  have hsum0 : (0:ℝ)≤d.sum := Nat.cast_nonneg _
  have ht0 : (0:ℝ)≤t := Nat.cast_nonneg _
  have hl0 : (0:ℝ)≤l := Nat.cast_nonneg _
  unfold zeroCountLayer
  simp only [List.sum_cons,Nat.cast_add]
  nlinarith [mul_nonneg hd0 ht0,mul_nonneg hd0 hsum0,mul_nonneg hd0 hl0]
end WP
namespace WP
open Set
lemma leading_adjacent_prefix_error_uniform (p : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ h : ℝ, 1≤h → ∀ t : ℕ, ∀ d : List ℕ, (t::d).length=p → ∀ N : ℕ, h/2 ≤ (N:ℝ)+1 →
      ∀ Y ∈ Icc (0:ℝ) y₀,
      |(∑ l ∈ Finset.range N, (A Y/h)*(weight Y l*zeroCountLayer t d l))-
        (degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h| ≤
      C*(((t::d).sum:ℝ)+1)^3/h^2 := by
  obtain ⟨B,hB,hA⟩ := genusExtension_A_uniform_upper
  obtain ⟨T,hT,hTail⟩ := Analysis.weight_polynomial_tail_uniform 1 2
  let K : ℝ := (p:ℝ)+4
  let C : ℝ := 4*B*K*T
  have hK : 0<K := by dsimp [K];positivity
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro h hh t d hd N hN Y hY
  have hhp : 0<h := by linarith
  have hA0 : 0 ≤ A Y := (div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num : (0:ℝ)<3)).le
  let f := fun l : ℕ => (A Y/h)*(weight Y l*zeroCountLayer t d l)
  have hpre₀ : HasSum (fun l : ℕ => if l<N then f l else 0)
      (∑ l ∈ Finset.range N, if l<N then f l else 0) :=
    hasSum_sum_of_ne_finset_zero (by
      intro l hl
      simp only [Finset.mem_range] at hl
      rw [if_neg hl])
  have hsum : (∑ l ∈ Finset.range N, if l<N then f l else 0)=∑ l ∈ Finset.range N, f l := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [if_pos (Finset.mem_range.mp hl)]
  rw [hsum] at hpre₀
  have hfull := degreeCorrection_adjacent_hasSum Y hY t d h
  change HasSum f _ at hfull
  have hTailSum : HasSum (fun l : ℕ => if N≤l then f l else 0)
      ((degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h-∑ l ∈ Finset.range N, f l) := by
    have heq : (fun l : ℕ => f l-(if l<N then f l else 0))=(fun l : ℕ => if N≤l then f l else 0) := by
      funext l
      by_cases hl : l<N
      · simp only [hl,ite_true,show ¬N≤l by omega,ite_false,sub_self]
      · simp only [hl,ite_false,show N≤l by omega,ite_true,sub_zero]
    rw [←heq]
    exact hfull.sub hpre₀
  have ht := hTail Y hY (t::d).sum N
  simp only [pow_one] at ht
  have hcount (l : ℕ) : zeroCountLayer t d l ≤ K*(((t::d).sum:ℝ)+l+1) := by
    have hi := zeroCountLayer_polynomial_bound t l d
    have hlen : (d.length:ℝ)+5=K := by
      have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
      dsimp [K]
      exact_mod_cast (show d.length+5=p+4 by omega)
    rwa [hlen] at hi
  have hpoint (l : ℕ) : (if N≤l then f l else 0) ≤
      ((A Y/h)*K)*(if N≤l then (((t::d).sum:ℝ)+l+1)*weight Y l else 0) := by
    by_cases hl : N≤l
    · simp only [hl,ite_true]
      dsimp [f]
      have hi := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcount l) (weight_nonneg Y hY l))
        (div_nonneg hA0 hhp.le)
      convert hi using 1 <;> simp only [List.sum_cons,Nat.cast_add] <;> ring
    · simp only [hl,ite_false,mul_zero,le_refl]
  have htail0 : 0 ≤ ∑'l:ℕ, if N≤l then f l else 0 := by
    apply tsum_nonneg
    intro l
    split_ifs
    · dsimp [f]
      exact mul_nonneg (div_nonneg hA0 hhp.le) (mul_nonneg (weight_nonneg Y hY l) (zeroCountLayer_nonneg t d l))
    · exact le_rfl
  have htailBound : (∑'l:ℕ, if N≤l then f l else 0) ≤
      ((A Y/h)*K)*(T*(((t::d).sum:ℝ)+1)/((N:ℝ)+1)^2) := by
    calc _ ≤ ∑'l:ℕ, ((A Y/h)*K)*(if N≤l then (((t::d).sum:ℝ)+l+1)*weight Y l else 0) :=
           hTailSum.summable.tsum_le_tsum hpoint (ht.1.mul_left _)
         _ = ((A Y/h)*K)*∑'l:ℕ, if N≤l then (((t::d).sum:ℝ)+l+1)*weight Y l else 0 := tsum_mul_left
         _ ≤ _ := mul_le_mul_of_nonneg_left ht.2 (by positivity)
  rw [abs_sub_comm,←hTailSum.tsum_eq,abs_of_nonneg htail0]
  have hD0 : (0:ℝ)≤(t::d).sum := Nat.cast_nonneg _
  have hNpos : 0<(N:ℝ)+1 := by positivity
  have hden : h^2 ≤ 4*(h*((N:ℝ)+1)^2) := by
    have hi := pow_le_pow_left₀ (show 0≤h/2 by positivity) hN 2
    have hhprod := mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg ((N:ℝ)+1))
    nlinarith
  have hD3 : ((t::d).sum:ℝ)+1 ≤ (((t::d).sum:ℝ)+1)^3 := by
    nlinarith [mul_nonneg hD0 (sq_nonneg (((t::d).sum:ℝ)+1))]
  calc _ ≤ ((A Y/h)*K)*(T*(((t::d).sum:ℝ)+1)/((N:ℝ)+1)^2) := htailBound
       _ = (A Y*K*T*(((t::d).sum:ℝ)+1))/(h*((N:ℝ)+1)^2) := by field_simp <;> ring
       _ ≤ (B*K*T*(((t::d).sum:ℝ)+1))/(h*((N:ℝ)+1)^2) := by
         apply div_le_div_of_nonneg_right _ (by positivity)
         have hi := mul_le_mul_of_nonneg_right (hA Y hY)
           (show 0≤K*T*(((t::d).sum:ℝ)+1) by positivity)
         simpa only [mul_assoc] using hi
       _ ≤ (4*B*K*T*(((t::d).sum:ℝ)+1))/h^2 := by
         apply (div_le_div_iff₀ (by positivity : 0<h*((N:ℝ)+1)^2) (sq_pos_of_pos hhp)).2
         have hi := mul_le_mul_of_nonneg_left hden (show 0≤B*K*T*(((t::d).sum:ℝ)+1) by positivity)
         nlinarith
       _ ≤ C*(((t::d).sum:ℝ)+1)^3/h^2 := by
         apply div_le_div_of_nonneg_right _ (sq_nonneg h)
         simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left hD3 hC.le
end WP
