import WPFormalization.HigherOrder.FiniteLossMajorant
/-! The genuine finite loss sums are dominated by the polynomial majorant tail. Pair counts contribute the explicit factor 2^r, absorbed by the uniform scalar choice b>=2B. Product and power coefficient comparisons retain the actual loss degree; the cases of minimum loss one and two are both proved. No analytic convergence or canonical coefficient bound is assumed. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def finiteLossSeries (L K:ℕ) (B:ℝ) (u a e:Series) : Series :=
  ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
    if L ≤ 2*j+s ∧ 2*j+s ≤ K then
      PowerSeries.C (B^(2*j+s))*(PowerSeries.X^(2*j+s)*(u^(2*j+s)*a^j*e)) else 0
lemma finiteLossSeries_coeff (L K:ℕ) (B:ℝ) (u a e:Series) :
    PowerSeries.coeff K (finiteLossSeries L K B u a e)=
      ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
        if L ≤ 2*j+s ∧ 2*j+s ≤ K then
          B^(2*j+s)*PowerSeries.coeff (K-(2*j+s)) (u^(2*j+s)*a^j*e) else 0 := by
  simp only[finiteLossSeries,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs with h
  · rw[PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul',if_pos h.2]
  · simp

lemma finiteLossSeries_coeff_le_counted (L K:ℕ) (B:ℝ) (hB:0 ≤ B) (u v a e E:Series)
    (hu:∀n,0 ≤ PowerSeries.coeff n u) (ha:∀n,0 ≤ PowerSeries.coeff n a)
    (he:∀n,0 ≤ PowerSeries.coeff n e)
    (huv:∀n,PowerSeries.coeff n u ≤ PowerSeries.coeff n v)
    (heE:∀n,PowerSeries.coeff n e ≤ PowerSeries.coeff n E) :
    PowerSeries.coeff K (finiteLossSeries L K B u a e) ≤
      ∑r∈Finset.range (K+1),if L ≤ r then (2*B)^r*
        PowerSeries.coeff (K-r) ((v*(1+a))^r*E) else 0 := by
  have hv:∀n,0 ≤ PowerSeries.coeff n v:=fun n=>(hu n).trans (huv n)
  have hE:∀n,0 ≤ PowerSeries.coeff n E:=fun n=>(he n).trans (heE n)
  have h1a:∀n,0 ≤ PowerSeries.coeff n (1+a):=by
    intro n
    rw[map_add]
    exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (ha n)
  let F:ℕ→ℝ:=fun r=>B^r*PowerSeries.coeff (K-r) ((v*(1+a))^r*E)
  have hF:∀r,0 ≤ F r:=by
    intro r
    exact mul_nonneg (pow_nonneg hB r) (coeff_mul_nonneg (coeff_pow_nonneg (coeff_mul_nonneg hv h1a) r) hE _)
  have hpoint (j s:ℕ) : B^(2*j+s)*PowerSeries.coeff (K-(2*j+s)) (u^(2*j+s)*a^j*e) ≤ F (2*j+s):=by
    have hm:=coeff_mul_mono (coeff_mul_nonneg (coeff_pow_nonneg hu (2*j+s)) (coeff_pow_nonneg ha j)) he
      (fun n=>coeff_mul_mono (coeff_pow_nonneg hu (2*j+s)) (coeff_pow_nonneg ha j)
        (coeff_pow_mono hu huv (2*j+s)) (coeff_power_le_one_add_power ha j (2*j+s) (by omega)) n)
      heE (K-(2*j+s))
    have hh:=mul_le_mul_of_nonneg_left hm (pow_nonneg hB (2*j+s))
    simpa only[F,mul_pow,mul_assoc] using hh
  rw[finiteLossSeries_coeff]
  calc
    _ ≤ ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
        if L ≤ 2*j+s ∧ 2*j+s ≤ K then F (2*j+s) else 0:=by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro s hs
      split_ifs
      · exact hpoint j s
      · exact le_rfl
    _ ≤ ∑r∈Finset.range (K+1),if L ≤ r then (2:ℝ)^r*F r else 0:=loss_pair_count_bound L K F hF
    _ = _:=by
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs
      · dsimp[F]
        rw[mul_pow]
        ring
      · rfl
lemma coefficient_nonnegative_C_X_mul (b:ℝ) (hb:0 ≤ b) (u:Series)
    (hu:∀n,0 ≤ PowerSeries.coeff n u) :
    ∀n,0 ≤ PowerSeries.coeff n (PowerSeries.C b*PowerSeries.X*u) := by
  have hC:∀n,0 ≤ PowerSeries.coeff n (PowerSeries.C b:Series):=by
    intro n
    rw[PowerSeries.coeff_C]
    split_ifs
    · exact hb
    · exact le_rfl
  have hX:∀n,0 ≤ PowerSeries.coeff n (PowerSeries.X:Series):=by
    intro n
    rw[PowerSeries.coeff_X]
    split_ifs<;>norm_num
  exact coeff_mul_nonneg (coeff_mul_nonneg hC hX) hu

lemma finiteLossSeries_coeff_le_power_tail (L K:ℕ) (B b:ℝ) (hB:0 ≤ B) (hb:2*B ≤ b)
    (u v a e E:Series) (hu:∀n,0 ≤ PowerSeries.coeff n u) (ha:∀n,0 ≤ PowerSeries.coeff n a)
    (he:∀n,0 ≤ PowerSeries.coeff n e)
    (huv:∀n,PowerSeries.coeff n u ≤ PowerSeries.coeff n v)
    (heE:∀n,PowerSeries.coeff n e ≤ PowerSeries.coeff n E) :
    PowerSeries.coeff K (finiteLossSeries L K B u a e) ≤
      PowerSeries.coeff K (E*(∑r∈Finset.range (K+1),if L ≤ r then
        (PowerSeries.C b*PowerSeries.X*(v*(1+a)))^r else 0)) := by
  have hv:∀n,0 ≤ PowerSeries.coeff n v:=fun n=>(hu n).trans (huv n)
  have hE:∀n,0 ≤ PowerSeries.coeff n E:=fun n=>(he n).trans (heE n)
  have h1a:∀n,0 ≤ PowerSeries.coeff n (1+a):=by
    intro n
    rw[map_add]
    exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (ha n)
  let Q:=PowerSeries.C b*PowerSeries.X*(v*(1+a))
  apply (finiteLossSeries_coeff_le_counted L K B hB u v a e E hu ha he huv heE).trans
  rw[Finset.mul_sum,map_sum]
  apply Finset.sum_le_sum
  intro r hr
  by_cases hL:L ≤ r
  · simp only[if_pos hL]
    have hp:E*Q^r=PowerSeries.C (b^r)*(PowerSeries.X^r*((v*(1+a))^r*E)):=by
      dsimp[Q]
      rw[mul_pow,mul_pow,←map_pow]
      ring
    change (2*B)^r*PowerSeries.coeff (K-r) ((v*(1+a))^r*E) ≤ PowerSeries.coeff K (E*Q^r)
    rw[hp,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul',if_pos (by have h:=Finset.mem_range.mp hr;omega)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ 2*B) hb r)
      (coeff_mul_nonneg (coeff_pow_nonneg (coeff_mul_nonneg hv h1a) r) hE _)
  · simp only[if_neg hL,mul_zero,map_zero,le_refl]

lemma finiteLossSeries_two_coeff_le_tail (K:ℕ) (B b:ℝ) (hB:0 ≤ B) (hb:2*B ≤ b)
    (u v a e E Z:Series) (hu:∀n,0 ≤ PowerSeries.coeff n u) (ha:∀n,0 ≤ PowerSeries.coeff n a)
    (he:∀n,0 ≤ PowerSeries.coeff n e)
    (huv:∀n,PowerSeries.coeff n u ≤ PowerSeries.coeff n v)
    (heE:∀n,PowerSeries.coeff n e ≤ PowerSeries.coeff n E)
    (hZpos:∀n,0 ≤ PowerSeries.coeff n Z)
    (hZ:Z=(PowerSeries.C b*PowerSeries.X*(v*(1+a)))^2+
      (PowerSeries.C b*PowerSeries.X*(v*(1+a)))*Z) :
    PowerSeries.coeff K (finiteLossSeries 2 K B u a e) ≤ PowerSeries.coeff K (E*Z) := by
  have hv:∀n,0 ≤ PowerSeries.coeff n v:=fun n=>(hu n).trans (huv n)
  have hE:∀n,0 ≤ PowerSeries.coeff n E:=fun n=>(he n).trans (heE n)
  have h1a:∀n,0 ≤ PowerSeries.coeff n (1+a):=by
    intro n
    rw[map_add]
    exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (ha n)
  have hQ:=coefficient_nonnegative_C_X_mul b (by linarith) (v*(1+a)) (coeff_mul_nonneg hv h1a)
  exact (finiteLossSeries_coeff_le_power_tail 2 K B b hB hb u v a e E hu ha he huv heE).trans
    (lossPartial_mul_coeff_le _ _ _ hQ hZpos hZ hE K K)
lemma lossPowerTail_one_coeff_le (Q Z:Series) (hQ:∀n,0 ≤ PowerSeries.coeff n Q)
    (hZpos:∀n,0 ≤ PowerSeries.coeff n Z) (hZ:Z=Q^2+Q*Z) (K n:ℕ) :
    PowerSeries.coeff n (∑r∈Finset.range (K+1),if 1 ≤ r then Q^r else 0) ≤
      PowerSeries.coeff n (Q+Z) := by
  have hsplit:(∑r∈Finset.range (K+1),if 1 ≤ r then Q^r else 0)=
      (∑r∈Finset.range (K+1),if r=1 then Q else 0)+
      (∑r∈Finset.range (K+1),if 2 ≤ r then Q^r else 0):=by
    rw[←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h0:r=0
    · subst r;simp
    by_cases h1:r=1
    · subst r;simp
    · simp only[if_pos (by omega : 1 ≤ r),if_neg h1,if_pos (by omega : 2 ≤ r),zero_add]
  have hfirst:(∑r∈Finset.range (K+1),if r=1 then Q else 0)=(if 1 ≤ K then Q else 0):=by
    by_cases hK:1 ≤ K
    · have hmem:(1:ℕ)∈Finset.range (K+1):=Finset.mem_range.mpr (by omega)
      simp only[Finset.sum_ite_eq',if_pos hmem,if_pos hK]
    · have hmem:(1:ℕ)∉Finset.range (K+1):=by simp only[Finset.mem_range];omega
      simp only[Finset.sum_ite_eq',if_neg hmem,if_neg hK]
  rw[hsplit,hfirst,←lossPartial_filtered]
  simp only[map_add]
  apply add_le_add
  · split_ifs
    · exact le_rfl
    · simpa only[map_zero] using hQ n
  · exact lossPartial_coeff_le Q Z hQ hZpos hZ (K-1) n

lemma finiteLossSeries_one_coeff_le_tail (K:ℕ) (B b:ℝ) (hB:0 ≤ B) (hb:2*B ≤ b)
    (u v a e E Z:Series) (hu:∀n,0 ≤ PowerSeries.coeff n u) (ha:∀n,0 ≤ PowerSeries.coeff n a)
    (he:∀n,0 ≤ PowerSeries.coeff n e)
    (huv:∀n,PowerSeries.coeff n u ≤ PowerSeries.coeff n v)
    (heE:∀n,PowerSeries.coeff n e ≤ PowerSeries.coeff n E)
    (hZpos:∀n,0 ≤ PowerSeries.coeff n Z)
    (hZ:Z=(PowerSeries.C b*PowerSeries.X*(v*(1+a)))^2+
      (PowerSeries.C b*PowerSeries.X*(v*(1+a)))*Z) :
    PowerSeries.coeff K (finiteLossSeries 1 K B u a e) ≤
      PowerSeries.coeff K (E*(PowerSeries.C b*PowerSeries.X*(v*(1+a))+Z)) := by
  have hv:∀n,0 ≤ PowerSeries.coeff n v:=fun n=>(hu n).trans (huv n)
  have hE:∀n,0 ≤ PowerSeries.coeff n E:=fun n=>(he n).trans (heE n)
  have h1a:∀n,0 ≤ PowerSeries.coeff n (1+a):=by
    intro n
    rw[map_add]
    exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (ha n)
  let Q:=PowerSeries.C b*PowerSeries.X*(v*(1+a))
  have hQ:=coefficient_nonnegative_C_X_mul b (by linarith) (v*(1+a)) (coeff_mul_nonneg hv h1a)
  have hTail:∀n,0 ≤ PowerSeries.coeff n (∑r∈Finset.range (K+1),if 1 ≤ r then Q^r else 0):=by
    intro n
    rw[map_sum]
    apply Finset.sum_nonneg
    intro r hr
    split_ifs
    · exact coeff_pow_nonneg hQ r n
    · simp
  exact (finiteLossSeries_coeff_le_power_tail 1 K B b hB hb u v a e E hu ha he huv heE).trans
    (coeff_mul_mono hE hTail (fun _=>le_rfl) (lossPowerTail_one_coeff_le Q Z hQ hZpos hZ K) K)
end WP.HigherOrder
