import WPFormalization.HigherOrder.CanonicalLastStep
import WPFormalization.HigherOrder.CanonicalSymmetryFromRemainder
/-! Compatibility on the common complex domain from genuine actual asymptotics.
At order K the increment uses the prescribed, already constructed order-(K-1) jet.
Real asymptotic uniqueness and holomorphic identity give permutation symmetry; moving
the distinguished coordinate to the last position preserves its ordered eraseIdx tail.
The actual uniform remainder remains an explicit unproved premise here. -/

noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open Set
lemma profileAtOrder_append_last (P : PsiTheory) (R : ℂ→ℂ) (Y : ℂ) (F : HierarchyJet) (K : ℕ)
    (d : List ℕ) (t : ℕ) :
    profileAtOrder P R Y F K (d ++ [t]) =
      (∑ i ∈ Finset.range d.length, ∑ s ∈ Finset.range d[i]!,
        adjacentCoefficient P R Y F K i (beforeCoordinate (d ++ [0]) i s)) +
      ∑ s ∈ Finset.range t, adjacentCoefficient P R Y F K d.length (d ++ [s]) := by
  unfold profileAtOrder
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ, append_last_getElem_bang]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [append_prefix_getElem_bang d t i hi']
    apply Finset.sum_congr rfl
    intro s hs
    rw [beforeCoordinate_append_last_independent d t 0 i s hi'.le]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [beforeCoordinate_append_last]

lemma profileAtOrder_append_last_step (P : PsiTheory) (R : ℂ→ℂ) (Y : ℂ) (F : HierarchyJet) (K : ℕ)
    (d : List ℕ) (t : ℕ) :
    profileAtOrder P R Y F K (d ++ [t + 1]) - profileAtOrder P R Y F K (d ++ [t]) =
      adjacentCoefficient P R Y F K d.length (d ++ [t]) := by
  rw [profileAtOrder_append_last, profileAtOrder_append_last, Finset.sum_range_succ]
  ring

lemma profileCoefficient_succ_rule (P:PsiTheory) (R:ℂ→ℂ) (Y:ℂ) (d:List ℕ) (k:ℕ) :
    profileCoefficient P R Y d (k+1)=profileAtOrder P R Y (hierarchyJet P R Y k) (k+1) d:=by
  change PowerSeries.coeff (k+1) (setCoeff ((hierarchyJet P R Y k).profile d) (k+1)
    (profileAtOrder P R Y (hierarchyJet P R Y k) (k+1) d))=_
  simp only[setCoeff,PowerSeries.coeff_mk,ite_true]

lemma canonical_append_last_increment (P:PsiTheory) (R:ℂ→ℂ) (Y:ℂ) (k:ℕ)
    (d:List ℕ) (t:ℕ) :
    profileCoefficient P R Y (d++[t+1]) (k+1)-profileCoefficient P R Y (d++[t]) (k+1)=
      adjacentCoefficient P R Y (hierarchyJet P R Y k) (k+1) d.length (d++[t]):=by
  rw[profileCoefficient_succ_rule,profileCoefficient_succ_rule,profileAtOrder_append_last_step]

lemma canonical_adjacent_on_complex_domain_of_recursiveRemainder
    (P:PsiTheory) (hr:WP.HigherOrder.UniformRecursiveRemainderTarget P)
    (Ω:Set ℂ) (hΩv:Convex ℝ Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R:ℂ→ℂ)
    (hA:∀j:ℕ,∀d:List ℕ,1 ≤ d.length→AnalyticOnNhd ℂ (fun z=>profileCoefficient P R z d j) Ω)
    (hrestrict:∀j:ℕ,∀d:List ℕ,1 ≤ d.length→∀Y∈Icc (0:ℝ) y₀,
      profileCoefficient P R (Y:ℂ) d j=(WP.HigherOrder.profileCoefficient P Y d j:ℂ))
    (K:ℕ) (hK:0<K) (d:List ℕ) (hd:1 ≤ d.length) (i:ℕ) (hi:i<d.length)
    (z:ℂ) (hz:z∈Ω) :
    profileCoefficient P R z (raiseDegree d i) K-profileCoefficient P R z d K=
      adjacentCoefficient P R z (hierarchyJet P R z (K-1)) K i d:=by
  cases K with
  | zero=>omega
  | succ k=>
    let e:=d.eraseIdx i
    let t:=d[i]!
    have ht:t=d[i]:=by simp[t,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    have hp0:d.Perm (e++[t]):=by
      have hp:(t::e).Perm d:=by simpa only[ht] using List.getElem_cons_eraseIdx_perm hi
      exact hp.symm.trans (by simpa only[List.singleton_append] using
        (List.perm_append_comm (l₁:=[t]) (l₂:=e)))
    have hp1:(raiseDegree d i).Perm (e++[t+1]):=by
      have hp:(raiseDegree d i).Perm ((t+1)::e):=List.set_perm_cons_eraseIdx hi (t+1)
      exact hp.trans (by simpa only[List.singleton_append] using
        (List.perm_append_comm (l₁:=[t+1]) (l₂:=e)))
    have hf0:=profileCoefficient_perm_on_complex_domain_of_recursiveRemainder P hr Ω hΩv hcover R
      hA hrestrict hp0 hd (k+1) hz
    have hf1:=profileCoefficient_perm_on_complex_domain_of_recursiveRemainder P hr Ω hΩv hcover R
      hA hrestrict hp1 (by simpa only[raiseDegree_length] using hd) (k+1) hz
    change profileCoefficient P R z d (k+1)=profileCoefficient P R z (e++[t]) (k+1) at hf0
    change profileCoefficient P R z (raiseDegree d i) (k+1)=profileCoefficient P R z (e++[t+1]) (k+1) at hf1
    rw[hf0,hf1,canonical_append_last_increment P R z k e t]
    simp only[adjacentCoefficient,append_last_getElem_bang,
      List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self,Nat.add_sub_cancel]
    simp only[List.eraseIdx_cons_zero,List.append_nil]
    rfl
end WP.HigherOrder.ComplexCanonical
