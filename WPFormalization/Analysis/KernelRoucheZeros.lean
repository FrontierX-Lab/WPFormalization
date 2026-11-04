import WPFormalization.Analysis.KernelRoucheBoundary
import WPFormalization.Analysis.FiniteSineRoots
import WPFormalization.Analysis.DeformedRealZeros
import WPFormalization.External.Rouche

/-! Complete reality, simplicity and ordered enumeration of the actual
deformed-kernel zeros. The characteristic signs construct the target zeros,
the exact sine catalog and actual boundary estimate verify every hypothesis
of the generic classical Rouche count, and increasing disks exhaust C.
The square coordinate then identifies the original positive K zeros and r. -/
noncomputable section
namespace WP.Analysis
open Set

def deformedSine (Y:ℝ) (t:ℂ) : ℂ := K Y ((t^2-4*Y)/2)
lemma deformedSine_differentiable (Y:ℝ) : Differentiable ℂ (deformedSine Y) := by
  unfold deformedSine
  exact (K_differentiable Y).comp (by fun_prop)
lemma deformedSine_even (Y:ℝ) (t:ℂ) : deformedSine Y (-t)=deformedSine Y t := by
  simp only [deformedSine,neg_sq]
lemma deformedSine_ofReal (Y t:ℝ) : deformedSine Y (t:ℂ)=K Y (((t^2-4*Y)/2:ℝ):ℂ) := by
  unfold deformedSine
  congr 1
  push_cast
  ring
lemma large_sine_disk (r:ℝ) (n:ℕ) : ∃N:ℕ,
    (100:ℝ) ≤ ((N:ℝ)+1/2)*Real.pi ∧ r<((N:ℝ)+1/2)*Real.pi ∧ n<N := by
  obtain ⟨N,hN⟩:=exists_nat_gt (max (n:ℝ) (max 100 r/Real.pi))
  have hn:n<N:=by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hr:max 100 r<(N:ℝ)*Real.pi:=
    (div_lt_iff₀ Real.pi_pos).mp (lt_of_le_of_lt (le_max_right _ _) hN)
  have hR:(N:ℝ)*Real.pi<((N:ℝ)+1/2)*Real.pi:=by nlinarith [Real.pi_pos]
  exact ⟨N,((le_max_left _ _).trans hr.le).trans hR.le,
    lt_of_le_of_lt (le_max_right _ _) (hr.trans hR),hn⟩
lemma deformedSine_finite_catalog (Y:ℝ) (hY:Y∈Ico 0 y₀)
    (u:ℕ→ℝ) (hmono:StrictMono u) (hpos:∀j,0<u j)
    (hbound:∀j,u j<((j:ℝ)+3/2)*Real.pi)
    (hzeros:∀j,K Y (((u j^2-4*Y)/2:ℝ):ℂ)=0)
    (N:ℕ) (hN:(100:ℝ) ≤ ((N:ℝ)+1/2)*Real.pi) :
    External.HasAllSimpleZerosInDisk (deformedSine Y) (((N:ℝ)+1/2)*Real.pi)
      (pairedRealRoots (fun i:Fin N=>u i.val)) := by
  let r:Fin N→ℝ:=fun i=>u i.val
  have href:External.HasAllSimpleZerosInDisk sineReference (((N:ℝ)+1/2)*Real.pi)
      (pairedRealRoots (positiveSineRoots N)) := pairedSineRoots_catalog N
  have hri:Function.Injective r:=fun i j hij=>Fin.ext (hmono.injective hij)
  have hrp:∀i,0<r i:=fun i=>hpos i.val
  have hboundary:∀ t:ℂ,‖t‖=((N:ℝ)+1/2)*Real.pi →
      ‖deformedSine Y t-sineReference t‖<‖sineReference t‖ := by
    intro t ht
    exact kernel_rouche_boundary Y ⟨hY.1,hY.2.le⟩ N hN t ht
  refine External.rouche_exhausts_prescribed_zeros
    (deformedSine Y) sineReference (deformedSine_differentiable Y) sineReference_differentiable
    _ (by positivity) hboundary (pairedRealRoots (positiveSineRoots N))
    (pairedRealRoots r) href (pairedRealRoots_injective r hrp hri) ?_
  intro i
  have hb (j:Fin N) : u j.val<((N:ℝ)+1/2)*Real.pi := by
    have hj:(j.val:ℝ)+1 ≤ N:=by exact_mod_cast (show j.val+1 ≤ N by omega)
    exact (hbound j.val).trans_le (mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le)
  cases i with
  | inl j =>
    change ‖(u j.val:ℂ)‖<_ ∧ deformedSine Y (u j.val:ℂ)=0
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos j.val),deformedSine_ofReal]
    exact ⟨hb j,hzeros j.val⟩
  | inr j =>
    change ‖-(u j.val:ℂ)‖<_ ∧ deformedSine Y (-(u j.val:ℂ))=0
    rw [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos j.val),
      deformedSine_even,deformedSine_ofReal]
    exact ⟨hb j,hzeros j.val⟩
lemma deformedSine_complete_zeros (Y:ℝ) (hY:Y∈Ico 0 y₀) :
    ∃u:ℕ→ℝ,StrictMono u ∧ (∀j,0<u j) ∧
      (∀t:ℂ,deformedSine Y t=0 ↔ ∃j,t=(u j:ℂ) ∨ t= -(u j:ℂ)) ∧
      (∀j,deriv (deformedSine Y) (u j:ℂ)≠0) := by
  obtain ⟨u,hmono,hpos,hbound,_,hzeros⟩:=deformed_positive_roots Y hY
  refine ⟨u,hmono,hpos,?_,?_⟩
  · intro t
    constructor
    · intro ht
      obtain ⟨N,hN,htN,_⟩:=large_sine_disk ‖t‖ 0
      obtain ⟨i,hi⟩ := (deformedSine_finite_catalog Y hY u hmono hpos hbound hzeros N hN).2.2 t htN ht
      cases i with
      | inl j => exact ⟨j.val,Or.inl hi⟩
      | inr j => exact ⟨j.val,Or.inr hi⟩
    · rintro ⟨j,ht | ht⟩
      · rw [ht,deformedSine_ofReal]
        exact hzeros j
      · rw [ht,deformedSine_even,deformedSine_ofReal]
        exact hzeros j
  · intro j
    obtain ⟨N,hN,_,hj⟩:=large_sine_disk ‖(u j:ℂ)‖ j
    exact (deformedSine_finite_catalog Y hY u hmono hpos hbound hzeros N hN).2.1 (Sum.inl ⟨j,hj⟩) |>.2.2
lemma deformedSine_hasDerivAt (Y:ℝ) (t:ℂ) :
    HasDerivAt (deformedSine Y) (t*deriv (K Y) ((t^2-4*Y)/2)) t := by
  have hd := ((K_differentiable Y _).hasDerivAt.comp t
    ((((hasDerivAt_id t).pow 2).sub_const (4*(Y:ℂ))).div_const 2))
  convert hd using 1
  · rfl
  · dsimp;ring
lemma K_ordered_simple_zeros (Y:ℝ) (hY:Y∈Ico 0 y₀) :
    ∃q:ℕ→ℝ,StrictMono q ∧ (∀j,0<q j) ∧ q 0=r Y ∧
      (∀z:ℂ,K Y z=0 ↔ ∃j,z=(q j:ℂ)) ∧
      (∀j,deriv (K Y) (q j:ℂ)≠0) := by
  obtain ⟨u,hmono,hpos,hall,hsimple⟩:=deformedSine_complete_zeros Y hY
  let q:ℕ→ℝ:=fun j=>(u j^2-4*Y)/2
  have hqroot (j:ℕ):K Y (q j:ℂ)=0 := by
    have hg:=((hall (u j:ℂ)).2 ⟨j,Or.inl rfl⟩)
    rw [deformedSine_ofReal] at hg
    exact hg
  have hqpos (j:ℕ):0<q j := by
    by_contra hh
    have hp:=K_nonpositive_re_pos Y (q j) hY.2 (le_of_not_gt hh)
    rw [hqroot j,Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hqmono:StrictMono q := by
    intro i j hij
    have hh:=mul_pos (sub_pos.mpr (hmono hij)) (add_pos (hpos j) (hpos i))
    dsimp [q]
    nlinarith
  have hqall (z:ℂ):K Y z=0 ↔ ∃j,z=(q j:ℂ) := by
    constructor
    · intro hz
      let t:ℂ:=Complex.sqrt (2*z+4*Y)
      have hs:t^2=2*z+4*Y:=complex_sqrt_sq _
      have ht:deformedSine Y t=0 := by
        unfold deformedSine
        rw [hs,show (2*z+4*(Y:ℂ)-4*Y)/2=z by ring]
        exact hz
      obtain ⟨j,hj⟩:=(hall t).mp ht
      have ht2:t^2=(u j:ℂ)^2:=by rcases hj with hj | hj <;> rw [hj] <;> simp only [neg_sq]
      refine ⟨j,?_⟩
      change z=(((u j^2-4*Y)/2:ℝ):ℂ)
      push_cast
      linear_combination (1/2:ℂ)*ht2-(1/2:ℂ)*hs
    · rintro ⟨j,rfl⟩
      exact hqroot j
  have hqfirst:q 0=r Y := by
    unfold r
    symm
    apply le_antisymm
    · exact csInf_le ⟨0,fun t ht=>ht.1.le⟩ ⟨hqpos 0,hqroot 0⟩
    · have hne:{t:ℝ | 0<t ∧ K Y t=0}.Nonempty:=⟨q 0,hqpos 0,hqroot 0⟩
      apply le_csInf hne
      intro t ht
      obtain ⟨j,hj⟩:=(hqall (t:ℂ)).mp ht.2
      have he:t=q j:=Complex.ofReal_inj.mp hj
      rw [he]
      exact hqmono.monotone (Nat.zero_le j)
  refine ⟨q,hqmono,hqpos,hqfirst,hqall,?_⟩
  intro j
  have hd:=deformedSine_hasDerivAt Y (u j:ℂ)
  have harg:((u j:ℂ)^2-4*Y)/2=(q j:ℂ):=by dsimp [q];push_cast;ring
  rw [harg] at hd
  have hn:=hsimple j
  rw [hd.deriv] at hn
  exact fun he=>hn (by rw [he,mul_zero])
end WP.Analysis
