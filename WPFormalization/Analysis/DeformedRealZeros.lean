import WPFormalization.Analysis.KernelRealSigns
import WPFormalization.Analysis.KernelSineReference

/-! An infinite strictly ordered sequence of actual positive characteristic
zeros. IVT and the proved signs give one zero before pi and two zeros in
each later positive sine interval. The slots are disjoint. Exhaustion and
simplicity are deliberately separate obligations for the Rouche argument. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology

def deformedSineReal (Y t : ℝ) : ℝ := (K Y (((t^2-4*Y)/2:ℝ):ℂ)).re
lemma deformedSineReal_continuous (Y : ℝ) : Continuous (deformedSineReal Y) := by
  unfold deformedSineReal
  apply Complex.continuous_re.comp
  exact (K_differentiable Y).continuous.comp (by fun_prop)
lemma deformedSineReal_at_nat_pi_negative (Y : ℝ) (hY:Y∈Ioo 0 y₀)
    (n:ℕ) (hn:1 ≤ n) : deformedSineReal Y ((n:ℝ)*Real.pi) < 0 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have htn : Real.pi ≤ (n:ℝ)*Real.pi := by nlinarith [mul_nonneg (sub_nonneg.mpr hnR) Real.pi_pos.le]
  apply deformedKernel_sine_zero_negative Y _ hY (Real.pi_pos.trans_le htn)
    (by nlinarith [Real.pi_gt_three,y₀_lt_three_halves,hY.2]) (Real.sin_nat_mul_pi n)
lemma deformedSineReal_at_midpoint_positive (Y:ℝ) (hY:Y∈Icc 0 y₀)
    (m:ℕ) (hm:1 ≤ m) : 0 < deformedSineReal Y ((2*(m:ℝ)+1/2)*Real.pi) := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have htm : Real.pi ≤ (m:ℝ)*Real.pi := by nlinarith [mul_nonneg (sub_nonneg.mpr hmR) Real.pi_pos.le]
  apply deformedKernel_sine_one_positive Y _ hY (by nlinarith [Real.pi_gt_three])
  rw [show (2*(m:ℝ)+1/2)*Real.pi=Real.pi/2+(m:ℝ)*(2*Real.pi) by ring,
    Real.sin_add_nat_mul_two_pi,Real.sin_pi_div_two]
lemma deformedSineReal_first_zero (Y:ℝ) (hY:Y∈Ioo 0 y₀) :
    ∃ t:ℝ,t∈Ioo 0 Real.pi ∧ deformedSineReal Y t=0 := by
  have h0:0 < deformedSineReal Y 0 := by
    change 0 < (K Y (((0^2-4*Y)/2:ℝ):ℂ)).re
    exact K_nonpositive_re_pos Y _ hY.2 (by nlinarith [hY.1])
  have hpi := deformedSineReal_at_nat_pi_negative Y hY 1 (by omega)
  simp only [Nat.cast_one,one_mul] at hpi
  exact intermediate_value_Ioo' Real.pi_pos.le
    (deformedSineReal_continuous Y).continuousOn ⟨hpi,h0⟩
lemma deformedSineReal_two_zeros (Y:ℝ) (hY:Y∈Ioo 0 y₀) (m:ℕ) (hm:1 ≤ m) :
    (∃ t:ℝ,t∈Ioo ((2*(m:ℝ))*Real.pi) ((2*(m:ℝ)+1/2)*Real.pi) ∧
      deformedSineReal Y t=0) ∧
    (∃ t:ℝ,t∈Ioo ((2*(m:ℝ)+1/2)*Real.pi) ((2*(m:ℝ)+1)*Real.pi) ∧
      deformedSineReal Y t=0) := by
  have hl := deformedSineReal_at_nat_pi_negative Y hY (2*m) (by omega)
  have hr := deformedSineReal_at_nat_pi_negative Y hY (2*m+1) (by omega)
  have hc := deformedSineReal_at_midpoint_positive Y ⟨hY.1.le,hY.2.le⟩ m hm
  push_cast at hl hr
  constructor
  · exact intermediate_value_Ioo (by nlinarith [Real.pi_pos])
      (deformedSineReal_continuous Y).continuousOn ⟨hl,hc⟩
  · exact intermediate_value_Ioo' (by nlinarith [Real.pi_pos])
      (deformedSineReal_continuous Y).continuousOn ⟨hr,hc⟩
lemma deformedSineReal_large_zero (Y : ℝ) (hY:Y∈Ioo 0 y₀) (k:ℕ) (hk:2 ≤ k) :
    ∃ t:ℝ,t∈Ioo (((k:ℝ)-1/2)*Real.pi) (((k:ℝ)+1/2)*Real.pi) ∧
      deformedSineReal Y t=0 := by
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m,hm⟩ := he
    have hm1 : 1 ≤ m := by omega
    obtain ⟨t,ht,hroot⟩ := (deformedSineReal_two_zeros Y hY m hm1).1
    refine ⟨t,?_,hroot⟩
    have hkR := congrArg (fun n:ℕ=>(n:ℝ)) hm
    push_cast at hkR
    rw [hkR]
    constructor <;> nlinarith [ht.1,ht.2,Real.pi_pos]
  · obtain ⟨m,hm⟩ := ho
    have hm1 : 1 ≤ m := by omega
    obtain ⟨t,ht,hroot⟩ := (deformedSineReal_two_zeros Y hY m hm1).2
    refine ⟨t,?_,hroot⟩
    have hkR := congrArg (fun n:ℕ=>(n:ℝ)) hm
    push_cast at hkR
    rw [hkR]
    constructor <;> nlinarith [ht.1,ht.2,Real.pi_pos]
lemma deformedSineReal_zero_in_slot (Y:ℝ) (hY:Y∈Ico 0 y₀) (j:ℕ) :
    ∃t:ℝ,0<t ∧ t<((j:ℝ)+3/2)*Real.pi ∧
      (j=0 ∨ ((j:ℝ)+1/2)*Real.pi<t) ∧ deformedSineReal Y t=0 := by
  by_cases hzero:Y=0
  · subst Y
    let t:ℝ:=((j:ℝ)+1)*Real.pi
    have hroot:sineReference (t:ℂ)=0 := by
      apply (sineReference_zero_iff _).2
      refine ⟨(j:ℤ)+1,by omega,?_⟩
      dsimp [t]
      push_cast
      ring
    have hr:deformedSineReal 0 t=0 := by
      dsimp [deformedSineReal]
      simp only [mul_zero,sub_zero]
      have he: (((t^2/2:ℝ):ℂ))=(t:ℂ)^2/2 := by push_cast;ring
      rw [he]
      change (sineReference (t:ℂ)).re=0
      rw [hroot,Complex.zero_re]
    refine ⟨t,by dsimp [t];positivity,?_,Or.inr ?_,hr⟩
    · dsimp [t];nlinarith [Real.pi_pos]
    · dsimp [t];nlinarith [Real.pi_pos]
  have hYpos:Y∈Ioo 0 y₀:=⟨lt_of_le_of_ne hY.1 (Ne.symm hzero),hY.2⟩
  by_cases hj:j=0
  · subst j
    obtain ⟨t,ht,hroot⟩ := deformedSineReal_first_zero Y hYpos
    refine ⟨t,ht.1,?_,Or.inl rfl,hroot⟩
    norm_num only [Nat.cast_zero,zero_add]
    nlinarith [ht.2,Real.pi_pos]
  · obtain ⟨t,ht,hroot⟩ := deformedSineReal_large_zero Y hYpos (j+1) (by omega)
    push_cast at ht
    refine ⟨t,?_,?_,Or.inr ?_,hroot⟩
    · have hjR:(1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      nlinarith [ht.1,Real.pi_pos,mul_nonneg (sub_nonneg.mpr hjR) Real.pi_pos.le]
    · nlinarith [ht.2]
    · nlinarith [ht.1]
lemma deformedSineReal_zero_complex (Y t:ℝ) (ht:deformedSineReal Y t=0) :
    K Y (((t^2-4*Y)/2:ℝ):ℂ)=0 := by
  apply Complex.ext
  · exact ht
  · simpa only [K,rootKernel,Complex.zero_im] using rootKernel_real Y ((t^2-4*Y)/2)
lemma deformed_positive_roots (Y:ℝ) (hY:Y∈Ico 0 y₀) :
    ∃u:ℕ→ℝ,StrictMono u ∧ (∀j,0<u j) ∧
      (∀j,u j<((j:ℝ)+3/2)*Real.pi) ∧
      (∀j:ℕ,j≠0 → ((j:ℝ)+1/2)*Real.pi<u j) ∧
      (∀j,K Y (((u j^2-4*Y)/2:ℝ):ℂ)=0) := by
  choose u hu using deformedSineReal_zero_in_slot Y hY
  refine ⟨u,?_,fun j=>(hu j).1,fun j=>(hu j).2.1,?_,?_⟩
  · intro i j hij
    have hj0:j≠0:=by omega
    have hl:=((hu j).2.2.1).resolve_left hj0
    have hc:(i:ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
    have hb:((i:ℝ)+3/2)*Real.pi ≤ ((j:ℝ)+1/2)*Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le
    exact (hu i).2.1.trans (hb.trans_lt hl)
  · intro j hj
    exact ((hu j).2.2.1).resolve_left hj
  · intro j
    exact deformedSineReal_zero_complex Y (u j) (hu j).2.2.2
end WP.Analysis
