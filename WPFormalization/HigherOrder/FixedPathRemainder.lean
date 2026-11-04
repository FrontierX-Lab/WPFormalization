import WPFormalization.HigherOrder.TriangularLocality
import WPFormalization.HigherOrder.SecondProfileGrowth
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.OrderWeights
/-! Actual profile errors telescope along the prescribed coordinate path.
The canonical finite profile prefix is identified exactly with its finite
adjacent coefficient sums. This yields the actual profile remainder from
edge residuals and a sharp path norm estimate, without assuming arbitrary
coordinate-path compatibility or the full C.3 remainder target. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries Set
lemma fixed_coordinate_path_telescope (F:List ℕ→ℝ) (d:List ℕ) :
    F d-F (List.replicate d.length 0)=
      ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,
        (F (beforeCoordinate d i (t+1))-F (beforeCoordinate d i t)) := by
  have hrow (i:ℕ) (hi:i∈Finset.range d.length) :
      (∑t∈Finset.range d[i]!,(F (beforeCoordinate d i (t+1))-F (beforeCoordinate d i t)))=
        F (beforeCoordinate d (i+1) 0)-F (beforeCoordinate d i 0) := by
    rw[Finset.sum_range_sub (fun t=>F (beforeCoordinate d i t)) _,beforeCoordinate_next d i (Finset.mem_range.mp hi)]
  rw[Finset.sum_congr rfl hrow,Finset.sum_range_sub (fun i=>F (beforeCoordinate d i 0)) d.length,beforeCoordinate_end,beforeCoordinate_zero]

def canonicalAdjacentTruncation (P:PsiTheory) (Y:ℝ) (L i:ℕ) (d:List ℕ) (t:ℝ) : ℝ :=
  ∑j∈Finset.range (L-1),adjacentCoefficient P Y (formalHierarchyJet P Y) (j+1) i d*t^(j+1)

lemma formal_profile_truncation_path (P:PsiTheory) (Y:ℝ) (L:ℕ) (hL:1≤L)
    (d:List ℕ) (t:ℝ) :
    truncationValue (formalProfile P Y d) L t=
      1+∑i∈Finset.range d.length,∑u∈Finset.range d[i]!,
        canonicalAdjacentTruncation P Y L i (beforeCoordinate d i u) t := by
  rw[show L=L-1+1 by omega]
  unfold truncationValue
  rw[Finset.sum_range_succ']
  simp only[formalProfile,PowerSeries.coeff_mk,profileCoefficient_zero,pow_zero,mul_one]
  have he (j:ℕ):profileCoefficient P Y d (j+1)=
      ∑i∈Finset.range d.length,∑u∈Finset.range d[i]!,
        adjacentCoefficient P Y (formalHierarchyJet P Y) (j+1) i (beforeCoordinate d i u) :=
    profileCoefficient_succ_recursion P Y d j
  simp_rw[he,Finset.sum_mul]
  rw[Finset.sum_comm]
  have hh : (∑i∈Finset.range d.length,∑j∈Finset.range (L-1),∑u∈Finset.range d[i]!,
      adjacentCoefficient P Y (formalHierarchyJet P Y) (j+1) i (beforeCoordinate d i u)*t^(j+1))=
      ∑i∈Finset.range d.length,∑u∈Finset.range d[i]!,
        canonicalAdjacentTruncation P Y (L-1+1) i (beforeCoordinate d i u) t := by
    apply Finset.sum_congr rfl
    intro i hi
    rw[Finset.sum_comm]
    rfl
  rw[hh]
  ring

lemma actual_profile_remainder_path (P:PsiTheory) (g L:ℕ) (hL:1≤L) (d:List ℕ)
    (hd:1≤d.length) (hs:Stable g d.length) (Y t:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    profile P g d Y-truncationValue (formalProfile P Y d) L t=
      ∑i∈Finset.range d.length,∑u∈Finset.range d[i]!,
        ((profile P g (beforeCoordinate d i (u+1)) Y-profile P g (beforeCoordinate d i u) Y)-
          canonicalAdjacentTruncation P Y L i (beforeCoordinate d i u) t) := by
  rw[formal_profile_truncation_path P Y L hL d t]
  have he:=fixed_coordinate_path_telescope (fun v=>profile P g v Y) d
  rw[profile_replicate_zero P g d.length hd hs Y hY] at he
  simp_rw[Finset.sum_sub_distrib] at he ⊢
  rw[←he]
  ring

lemma profile_remainder_bound_of_path_edges (P:PsiTheory) (g L:ℕ) (hL:1≤L) (d:List ℕ)
    (hd:1≤d.length) (hs:Stable g d.length) (Y t M B:ℝ) (hY:Y∈Icc (0:ℝ) y₀)
    (ht:0≤t) (hM:0≤M) (hB:0≤B)
    (hedge:∀i∈Finset.range d.length,∀u∈Finset.range d[i]!,
      |(profile P g (beforeCoordinate d i (u+1)) Y-profile P g (beforeCoordinate d i u) Y)-
        canonicalAdjacentTruncation P Y L i (beforeCoordinate d i u) t|≤
        B*profileOrderWeight M L (beforeCoordinate d i u)^(2*L-1)*t^L) :
    |profile P g d Y-truncationValue (formalProfile P Y d) L t|≤
      B*profileOrderWeight M L d^(2*L)*t^L := by
  let S:ℝ:=profileOrderWeight M L d
  have hS:0≤S:=by dsimp[S,profileOrderWeight];positivity
  have hlookup : (∑i∈Finset.range d.length,(d[i]!:ℝ))=(d.sum:ℝ) := by
    rw[sum_range_getElem]
    exact (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
  have hterm (i:ℕ) (hi:i∈Finset.range d.length) (u:ℕ) (hu:u∈Finset.range d[i]!) :
      |(profile P g (beforeCoordinate d i (u+1)) Y-profile P g (beforeCoordinate d i u) Y)-
        canonicalAdjacentTruncation P Y L i (beforeCoordinate d i u) t|≤B*S^(2*L-1)*t^L := by
    have hsum : ((beforeCoordinate d i u).sum:ℝ)≤d.sum := by
      exact_mod_cast beforeCoordinate_sum_le d i u (Finset.mem_range.mp hi) (Finset.mem_range.mp hu).le
    have hw:profileOrderWeight M L (beforeCoordinate d i u)≤S := by
      dsimp[S,profileOrderWeight]
      rw[beforeCoordinate_length]
      linarith
    have hw0:0≤profileOrderWeight M L (beforeCoordinate d i u):=by unfold profileOrderWeight;positivity
    exact (hedge i hi u hu).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hw _) hB) (pow_nonneg ht L))
  rw[actual_profile_remainder_path P g L hL d hd hs Y t hY]
  calc
    _≤∑i∈Finset.range d.length,|∑u∈Finset.range d[i]!,
        ((profile P g (beforeCoordinate d i (u+1)) Y-profile P g (beforeCoordinate d i u) Y)-
          canonicalAdjacentTruncation P Y L i (beforeCoordinate d i u) t)|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑i∈Finset.range d.length,∑u∈Finset.range d[i]!,
        |(profile P g (beforeCoordinate d i (u+1)) Y-profile P g (beforeCoordinate d i u) Y)-
          canonicalAdjacentTruncation P Y L i (beforeCoordinate d i u) t|:=
      Finset.sum_le_sum (fun i hi=>Finset.abs_sum_le_sum_abs _ _)
    _≤∑i∈Finset.range d.length,∑u∈Finset.range d[i]!,B*S^(2*L-1)*t^L:=
      Finset.sum_le_sum (fun i hi=>Finset.sum_le_sum (fun u hu=>hterm i hi u hu))
    _=(d.sum:ℝ)*(B*S^(2*L-1)*t^L):=by
      simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw[←Finset.sum_mul,hlookup]
    _≤S*(B*S^(2*L-1)*t^L):=mul_le_mul_of_nonneg_right
      (by dsimp[S,profileOrderWeight];linarith[Nat.cast_nonneg (α:=ℝ) d.length,mul_nonneg hM (Nat.cast_nonneg L)]) (by positivity)
    _=B*S^(2*L)*t^L:=by
      calc
        _=B*(S^(2*L-1)*S)*t^L:=by ring
        _=B*S^((2*L-1)+1)*t^L:=by rw[pow_succ]
        _=_:=by rw[show 2*L-1+1=2*L by omega]
end WP.HigherOrder
