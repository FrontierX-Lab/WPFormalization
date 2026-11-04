import WPFormalization.HigherOrder.AuxiliaryMajorantEquations
import WPFormalization.HigherOrder.ComplexHierarchyStability
import WPFormalization.HigherOrder.ComplexGenusMajorant
import WPFormalization.HigherOrder.ComplexSeparatingMajorant
set_option maxHeartbeats 800000
/-! The explicit finite-stage norm induction invariant for the genuine complex canonical hierarchy. The base jet satisfies it, the high-genus and p=1 bounds give the combined genus majorant, and actual adjacent coefficient bounds integrate along the fixed coordinate path with exactly one Sj factor. This module does not postulate the invariant for future stages. -/
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

def JetMajorantInvariant (M:ℝ) (N:ℕ) (F:HierarchyJet) (U:Fin 7→WP.HigherOrder.Series) : Prop :=
  (∀i:ℕ,i ≤ N→∀d:List ℕ,1 ≤ d.length→‖PowerSeries.coeff i (F.profile d)‖ ≤
    (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 2)) ∧
  (∀i:ℕ,i ≤ N→∀p:ℕ,1 ≤ p→‖PowerSeries.coeff i (F.cusp p)‖ ≤
    (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 3)) ∧
  (∀i:ℕ,i ≤ N→∀p:ℕ,2 ≤ p→‖PowerSeries.coeff i (F.genus p)‖ ≤
    (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 4)) ∧
  (∀i:ℕ,i ≤ N→‖PowerSeries.coeff i (F.genus 1)‖ ≤
    (scalarOrderWeight M i 1)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 6))

lemma auxiliarySolutionUnit_coeff_zero (U:Fin 7→WP.HigherOrder.Series) (h0:zeroConstant U) (i:Fin 7) :
    PowerSeries.coeff 0 (auxiliarySolutionUnit U i)=1 := by
  have hz:PowerSeries.constantCoeff (U i)=0:=by simpa only[←PowerSeries.coeff_zero_eq_constantCoeff] using h0 i
  simp[auxiliarySolutionUnit,hz]
lemma baseJet_majorant_invariant (M:ℝ) (U:Fin 7→WP.HigherOrder.Series) (h0:zeroConstant U) :
    JetMajorantInvariant M 0 baseJet U := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    intro i hi
    have hz:i=0:=by omega
    subst i
  · intro d hd;simp[baseJet,auxiliarySolutionUnit_coeff_zero U h0]
  · intro p hp;simp[baseJet,auxiliarySolutionUnit_coeff_zero U h0]
  · intro p hp;simp[baseJet,auxiliarySolutionUnit_coeff_zero U h0]
  · simp[baseJet,auxiliarySolutionUnit_coeff_zero U h0]

lemma JetMajorantInvariant.genus_all {M:ℝ} (hM:0 ≤ M) {N:ℕ} {F:HierarchyJet}
    {U:Fin 7→WP.HigherOrder.Series} (hI:JetMajorantInvariant M N F U)
    (hU:∀i j,0 ≤ PowerSeries.coeff j (U i)) (i:ℕ) (hi:i ≤ N) (p:ℕ) (hp:1 ≤ p) :
    ‖PowerSeries.coeff i (F.genus p)‖ ≤ (scalarOrderWeight M i p)^(2*i)*
      PowerSeries.coeff i (auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6) := by
  have hpow:0 ≤ (scalarOrderWeight M i p)^(2*i):=by unfold scalarOrderWeight;positivity
  rw[map_add]
  by_cases h1:p=1
  · subst p
    apply (hI.2.2.2 i hi).trans
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (auxiliarySolutionUnit_nonnegative U hU 4 i)) hpow
  · apply (hI.2.2.1 i hi p (by omega)).trans
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (auxiliarySolutionUnit_nonnegative U hU 6 i)) hpow

lemma profileAtOrder_norm_bound_of_adjacent (P:PsiTheory) (R:ℂ→ℂ) (z:ℂ) (F:HierarchyJet)
    (M:ℝ) (hM:0 ≤ M) (K:ℕ) (hK:1 ≤ K) (A:ℝ) (hA:0 ≤ A)
    (hinc:∀v:List ℕ,1 ≤ v.length→∀i:ℕ,i<v.length→
      ‖adjacentCoefficient P R z F K i v‖ ≤ (profileOrderWeight M K v)^(2*K-1)*A)
    (d:List ℕ) (hd:1 ≤ d.length) :
    ‖profileAtOrder P R z F K d‖ ≤ (profileOrderWeight M K d)^(2*K)*A := by
  let S:=profileOrderWeight M K d
  have hS0:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hterm (i:ℕ) (hi:i∈Finset.range d.length) (t:ℕ) (ht:t∈Finset.range d[i]!) :
      ‖adjacentCoefficient P R z F K i (beforeCoordinate d i t)‖ ≤ S^(2*K-1)*A:=by
    have hiv:i<(beforeCoordinate d i t).length:=by
      simpa only[beforeCoordinate_length] using Finset.mem_range.mp hi
    have hb:=hinc (beforeCoordinate d i t) (by simpa only[beforeCoordinate_length] using hd) i hiv
    have hsum:((beforeCoordinate d i t).sum:ℝ) ≤ d.sum:=by
      exact_mod_cast beforeCoordinate_sum_le d i t (Finset.mem_range.mp hi) (Finset.mem_range.mp ht).le
    have hw:profileOrderWeight M K (beforeCoordinate d i t) ≤ S:=by
      dsimp[S,profileOrderWeight]
      rw[beforeCoordinate_length]
      linarith
    have hw0:0 ≤ profileOrderWeight M K (beforeCoordinate d i t):=by unfold profileOrderWeight;positivity
    exact hb.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw _) hA)
  have hlookup:(∑i∈Finset.range d.length,(d[i]!:ℝ))=(d.sum:ℝ):=by
    rw[sum_range_getElem]
    exact (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
  unfold profileAtOrder
  calc
    _ ≤ ∑i∈Finset.range d.length,‖∑t∈Finset.range d[i]!,adjacentCoefficient P R z F K i (beforeCoordinate d i t)‖:=norm_sum_le _ _
    _ ≤ ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,‖adjacentCoefficient P R z F K i (beforeCoordinate d i t)‖:=
      Finset.sum_le_sum (fun i hi=>norm_sum_le _ _)
    _ ≤ ∑i∈Finset.range d.length,∑t∈Finset.range d[i]!,S^(2*K-1)*A:=
      Finset.sum_le_sum (fun i hi=>Finset.sum_le_sum (fun t ht=>hterm i hi t ht))
    _=(d.sum:ℝ)*(S^(2*K-1)*A):=by
      simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw[←Finset.sum_mul,hlookup]
    _ ≤ S*(S^(2*K-1)*A):=mul_le_mul_of_nonneg_right
      (canonical_path_count_le_order_weight M hM K d) (mul_nonneg (pow_nonneg hS0 _) hA)
    _=_:=by
      change S*(S^(2*K-1)*A)=S^(2*K)*A
      calc
        _=S^((2*K-1)+1)*A:=by rw[pow_succ];ring
        _=_:=by rw[show (2*K-1)+1=2*K by omega]
end WP.HigherOrder.ComplexCanonical
