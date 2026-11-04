import WPFormalization.HigherOrder.ComplexSeparatingMajorant
import WPFormalization.HigherOrder.RationalMajorantAlgebra
/-! Finite loss reindexing and the genuine polynomial loss-tail equation. The number of pairs 2j+s=r is bounded by 2^r, and every finite tail of powers of a nonnegative Q is coefficientwise bounded by a nonnegative solution Z=Q²+QZ. No convergence or hierarchy domination is assumed. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma loss_pair_count_bound (L K:ℕ) (F:ℕ→ℝ) (hF:∀r,0 ≤ F r) :
    (∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
      if L ≤ 2*j+s ∧ 2*j+s ≤ K then F (2*j+s) else 0) ≤
      ∑r∈Finset.range (K+1),if L ≤ r then (2:ℝ)^r*F r else 0 := by
  classical
  let P:=((Finset.range (K+1)).product (Finset.range (K+1))).filter
    (fun p:ℕ×ℕ=>L ≤ 2*p.1+p.2 ∧ 2*p.1+p.2 ≤ K)
  let loss:ℕ×ℕ→ℕ:=fun p=>2*p.1+p.2
  have hcard (r:ℕ) : ((P.filter (fun p=>loss p=r)).card:ℝ) ≤ (2:ℝ)^r := by
    let D:=P.filter (fun p=>loss p=r)
    have hinj:Set.InjOn Prod.fst (D:Set (ℕ×ℕ)):=by
      intro a ha b hb hab
      have hla:loss a=r:=(Finset.mem_filter.mp ha).2
      have hlb:loss b=r:=(Finset.mem_filter.mp hb).2
      apply Prod.ext hab
      dsimp[loss] at hla hlb
      omega
    have hsub:D.image Prod.fst⊆Finset.range (r+1):=by
      intro j hj
      obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hj
      have hl:loss p=r:=(Finset.mem_filter.mp hp).2
      dsimp[loss] at hl
      apply Finset.mem_range.mpr
      omega
    have hc:D.card ≤ r+1:=by
      calc D.card=(D.image Prod.fst).card:=(Finset.card_image_iff.mpr hinj).symm
        _ ≤ (Finset.range (r+1)).card:=Finset.card_le_card hsub
        _=r+1:=Finset.card_range _
    exact (show (D.card:ℝ) ≤ (r+1:ℕ) by exact_mod_cast hc).trans
      (by exact_mod_cast r.lt_two_pow_self.succ_le)
  have hm:∀p∈P,loss p∈Finset.range (K+1):=by
    intro p hp
    have hl:=(Finset.mem_filter.mp hp).2.2
    exact Finset.mem_range.mpr (by dsimp[loss];omega)
  have hfib:=Finset.sum_fiberwise_of_maps_to hm (fun p=>F (loss p))
  have hsum:(∑p∈P,F (loss p))=
      ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
        if L ≤ 2*j+s ∧ 2*j+s ≤ K then F (2*j+s) else 0:=by
    simp only[P,Finset.sum_filter,loss]
    exact Finset.sum_product _ _ _
  rw[←hsum,←hfib]
  apply Finset.sum_le_sum
  intro r hr
  by_cases h2:L ≤ r
  · rw[if_pos h2]
    calc
      _=∑p∈P.filter (fun p=>loss p=r),F r:=by
        apply Finset.sum_congr rfl
        intro p hp
        rw[(Finset.mem_filter.mp hp).2]
      _=((P.filter (fun p=>loss p=r)).card:ℝ)*F r:=by simp only[Finset.sum_const,nsmul_eq_mul]
      _ ≤ _:=mul_le_mul_of_nonneg_right (hcard r) (hF r)
  · rw[if_neg h2]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro p hp
    have hl:=(Finset.mem_filter.mp hp).2
    have hP:=(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    dsimp[loss] at hl
    omega

def lossPartial (Q:Series) (k:ℕ) : Series := ∑r∈Finset.range k,Q^(r+2)
lemma lossPartial_remainder (Q Z:Series) (hZ:Z=Q^2+Q*Z) (k:ℕ) :
    Z=lossPartial Q k+Q^k*Z := by
  induction k with
  | zero=>simp[lossPartial]
  | succ k ih=>
    calc
      Z=lossPartial Q k+Q^k*Z:=ih
      _=lossPartial Q k+Q^k*(Q^2+Q*Z):=congrArg (fun z=>lossPartial Q k+Q^k*z) hZ
      _=lossPartial Q (k+1)+Q^(k+1)*Z:=by
        simp only[lossPartial,Finset.sum_range_succ,pow_add,pow_succ]
        ring
lemma lossPartial_coeff_le (Q Z:Series) (hQ:∀n,0 ≤ PowerSeries.coeff n Q)
    (hZpos:∀n,0 ≤ PowerSeries.coeff n Z) (hZ:Z=Q^2+Q*Z) (k n:ℕ) :
    PowerSeries.coeff n (lossPartial Q k) ≤ PowerSeries.coeff n Z := by
  have hr:=congrArg (PowerSeries.coeff n) (lossPartial_remainder Q Z hZ k)
  simp only[map_add] at hr
  have hp:=coeff_mul_nonneg (coeff_pow_nonneg hQ k) hZpos n
  linarith
lemma lossPartial_filtered (Q:Series) (K:ℕ) :
    lossPartial Q (K-1)=∑r∈Finset.range (K+1),if 2 ≤ r then Q^r else 0 := by
  have hset:{r∈Finset.range (K+1)|2 ≤ r}=Finset.Ico 2 (K+1):=by
    ext r
    simp only[Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw[←Finset.sum_filter,hset]
  rw[Finset.sum_Ico_eq_sum_range]
  have hk:K+1-2=K-1:=by omega
  rw[hk]
  unfold lossPartial
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  omega

lemma lossPartial_mul_coeff_le (Q Z E:Series) (hQ:∀n,0 ≤ PowerSeries.coeff n Q)
    (hZpos:∀n,0 ≤ PowerSeries.coeff n Z) (hZ:Z=Q^2+Q*Z)
    (hE:∀n,0 ≤ PowerSeries.coeff n E) (K n:ℕ) :
    PowerSeries.coeff n (E*(∑r∈Finset.range (K+1),if 2 ≤ r then Q^r else 0)) ≤
      PowerSeries.coeff n (E*Z) := by
  rw[←lossPartial_filtered]
  have hp:∀j,0 ≤ PowerSeries.coeff j (lossPartial Q (K-1)):=by
    intro j
    simp only[lossPartial,map_sum]
    exact Finset.sum_nonneg (fun r hr=>coeff_pow_nonneg hQ (r+2) j)
  exact coeff_mul_mono hE hp (fun _=>le_rfl) (lossPartial_coeff_le Q Z hQ hZpos hZ (K-1)) n
end WP.HigherOrder
