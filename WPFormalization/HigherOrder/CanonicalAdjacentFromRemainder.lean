import WPFormalization.HigherOrder.CanonicalLastStep
import WPFormalization.HigherOrder.CanonicalSymmetryFromRemainder
import WPFormalization.HigherOrder.CoordinatePathCoherence
/-! Every-coordinate compatibility follows from genuine canonical asymptotics.
The only paper goal premise is the still-unproved uniform recursive remainder target.
This producer is not an inhabitant of that target and is not associated to C.3. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma canonical_adjacent_compatibility_of_recursiveRemainder (P:PsiTheory)
    (hr:UniformRecursiveRemainderTarget P) : CanonicalAdjacentCompatibility P := by
  intro Y hY K hK d hd i hi
  let e:=d.eraseIdx i
  let t:=d[i]!
  have ht:t=d[i]:=by
    simp[t,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  have hp0:d.Perm (e++[t]):=by
    have hp:(t::e).Perm d:=by simpa only[ht] using List.getElem_cons_eraseIdx_perm hi
    exact hp.symm.trans (by simpa only[List.singleton_append] using
      (List.perm_append_comm (l₁:=[t]) (l₂:=e)))
  have hp1:(raiseDegree d i).Perm (e++[t+1]):=by
    have hp:(raiseDegree d i).Perm ((t+1)::e):=
      List.set_perm_cons_eraseIdx hi (t+1)
    exact hp.trans (by simpa only[List.singleton_append] using
      (List.perm_append_comm (l₁:=[t+1]) (l₂:=e)))
  have hf0:=congrFun (profileCoefficient_perm_of_recursiveRemainder P hr hp0 hd Y hY) K
  have hf1:=congrFun (profileCoefficient_perm_of_recursiveRemainder P hr hp1
    (by simpa only[raiseDegree_length] using hd) Y hY) K
  rw[hf0,hf1,canonical_append_last_increment P Y K hK e t]
  simp only[adjacentCoefficient,append_last_getElem_bang,
    List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self]
  simp only[List.eraseIdx_cons_zero,List.append_nil]
  rfl
end WP.HigherOrder
