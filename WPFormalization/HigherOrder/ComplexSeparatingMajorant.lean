import WPFormalization.HigherOrder.ComplexSeparatingLabelMajorant
/-! The full actual complex separating operator, including every label subset and stability/loss guard. Cardinality fibers use the genuine binomial/Gamma count, and the degree-K norm is bounded on the precise Sj^(2K-1) scale by a finite nonnegative loss majorant. Local lower-order coefficient and true bounded-component Gamma data remain explicit. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma sum_powerset_by_card_truncated {𝕜:Type*} [AddCommMonoid 𝕜] (U:Finset ℕ) (K:ℕ)
    (f:Finset ℕ→𝕜) (hzero:∀I∈U.powerset,K<I.card→f I=0) :
    ∑I∈U.powerset,f I=∑s∈Finset.range (K+1),∑I∈Finset.powersetCard s U,f I := by
  classical
  have hf:=Finset.sum_fiberwise_eq_sum_filter U.powerset (Finset.range (K+1)) Finset.card f
  have hfilter (s:ℕ) : {I∈U.powerset|I.card=s}=Finset.powersetCard s U:=by
    ext I
    simp only[Finset.mem_filter,Finset.mem_powerset,Finset.mem_powersetCard]
  simp_rw[hfilter] at hf
  rw[hf]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hnI
  apply hzero I hI
  have hh:¬I.card∈Finset.range (K+1):=by simpa only[Finset.mem_filter,hI,true_and] using hnI
  have hcard:K+1 ≤ I.card:=by simpa only[Finset.mem_range,not_lt] using hh
  omega

lemma separatingSeries_sum_by_card (P:PsiTheory) (R:ℂ→ℂ) (z:ℂ) (F:HierarchyJet)
    (K t:ℕ) (d:List ℕ) :
    separatingSeries P R z F K t d=
      ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
        if Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ K then
          ∑I∈Finset.powersetCard s (Finset.range d.length),separatingConfiguration P R z F j t d I
        else 0 := by
  unfold separatingSeries
  apply Finset.sum_congr rfl
  intro j hj
  rw[sum_powerset_by_card_truncated (Finset.range d.length) K _ (by
    intro I hI hcard
    rw[if_neg (by omega)])]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h:Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ K
  · rw[if_pos h]
    apply Finset.sum_congr rfl
    intro I hI
    have hc:=(Finset.mem_powersetCard.mp hI).2
    rw[hc,if_pos h]
    simp only[separatingConfiguration,hc]
  · rw[if_neg h]
    apply Finset.sum_eq_zero
    intro I hI
    have hc:=(Finset.mem_powersetCard.mp hI).2
    rw[hc,if_neg h]

def separatingMajorant (K:ℕ) (B:ℝ) (e g a:WP.HigherOrder.Series) : WP.HigherOrder.Series :=
  ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
    if 2 ≤ 2*j+s ∧ 2*j+s ≤ K then
      PowerSeries.C (B^(2*j+s))*(PowerSeries.X^(2*j+s)*
        (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*((PowerSeries.exp ℝ)*e)))
    else 0
lemma separatingMajorant_coeff (K:ℕ) (B:ℝ) (e g a:WP.HigherOrder.Series) :
    PowerSeries.coeff K (separatingMajorant K B e g a)=
      ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
        if 2 ≤ 2*j+s ∧ 2*j+s ≤ K then B^(2*j+s)*
          PowerSeries.coeff (K-(2*j+s)) (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*((PowerSeries.exp ℝ)*e)) else 0 := by
  simp only[separatingMajorant,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs with h
  · rw[PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul',if_pos h.2]
  · simp
lemma separatingSeries_norm_majorant (ρ K₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) :
    ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧ ∀R:ℂ→ℂ,∀z:ℂ,
      (∀l:ℕ,‖WP.Analysis.complexWeightCoeff R l z‖ ≤ K₀/ρ^l)→
      ∀M:ℝ,M₀ ≤ M→∀K:ℕ,∀F:HierarchyJet,∀e g a:WP.HigherOrder.Series,
      (∀n:ℕ,0 ≤ PowerSeries.coeff n e)→(∀n:ℕ,0 ≤ PowerSeries.coeff n g)→(∀n:ℕ,0 ≤ PowerSeries.coeff n a)→
      (∀i:ℕ,i ≤ K-1→∀d:List ℕ,1 ≤ d.length→‖PowerSeries.coeff i (F.profile d)‖ ≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      (∀i:ℕ,i ≤ K-1→∀q:ℕ,1 ≤ q→‖PowerSeries.coeff i (F.cusp q)‖ ≤
        (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i g)→
      (∀i:ℕ,i ≤ K-1→∀q:ℕ,1 ≤ q→‖PowerSeries.coeff i (F.genus q)‖ ≤
        (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i a)→
      ∀P:PsiTheory,∀T:ℝ,1 ≤ T→
        (∀j:ℕ,∀d:List ℕ,Stable j d.length→‖smallW P R z j d‖ ≤
          Real.Gamma (complexity j d.length:ℝ)*T^(complexity j d.length))→
        ∀t:ℕ,∀d:List ℕ,
        ‖PowerSeries.coeff K (separatingSeries P R z F K t d)‖ ≤
          C*(profileOrderWeight M K (t::d))^(2*K-1)*
            PowerSeries.coeff K (separatingMajorant K (T*‖kernelA R z‖) e g a) := by
  obtain ⟨C,M₁,hC,hM₁,hlayer⟩:=separating_label_layer_norm_majorant ρ K₀ hρ hK₀
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro R z hgeom M hM K F e g a he hg ha hprofile hcusp hgenus P T hT hsmall t d
  have hMop:M₁ ≤ M:=(le_max_left _ _).trans hM
  have hM1:1 ≤ M:=(le_max_right _ _).trans hM
  have hM0:0 ≤ M:=by linarith
  let S:=profileOrderWeight M K (t::d)
  let B:=T*‖kernelA R z‖
  have hB:0 ≤ B:=mul_nonneg (by linarith) (norm_nonneg _)
  have hS1:1 ≤ S:=by
    have hMK:0 ≤ M*(K:ℝ):=by positivity
    dsimp[S,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) d.length]
  have hS0:0 ≤ S:=by linarith
  have hQ (j s:ℕ) : 0 ≤ PowerSeries.coeff (K-(2*j+s))
      (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*((PowerSeries.exp ℝ)*e)):=by
    have hExp2:∀k,0 ≤ PowerSeries.coeff k ((PowerSeries.exp ℝ)^2):=by
      simpa only[pow_two] using coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg
    exact coeff_mul_nonneg (coeff_mul_nonneg
      (coeff_pow_nonneg (coeff_mul_nonneg hExp2 hg) (2*j+s)) (coeff_pow_nonneg ha j))
      (coeff_mul_nonneg exp_coeff_nonneg he) _
  have hterm (j s:ℕ) :
      ‖PowerSeries.coeff K (if Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ K then
        ∑I∈Finset.powersetCard s (Finset.range d.length),separatingConfiguration P R z F j t d I else 0)‖ ≤
      C*S^(2*K-1)*(if 2 ≤ 2*j+s ∧ 2*j+s ≤ K then B^(2*j+s)*
        PowerSeries.coeff (K-(2*j+s)) (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*((PowerSeries.exp ℝ)*e)) else 0):=by
    by_cases h:Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ K
    · rw[if_pos h,if_pos h.2,map_sum]
      have hb:=hlayer R z hgeom M hMop K F e g a he hg ha hprofile hcusp hgenus
        P T hT hsmall j s t d h.1 h.2.1 h.2.2 (K-(2*j+s)) (by omega)
      rw[Nat.sub_add_cancel h.2.2] at hb
      apply ((norm_sum_le _ _).trans hb).trans
      have hp:S^(2*(K-(2*j+s))+(2*j+s)+1) ≤ S^(2*K-1):=
        pow_le_pow_right₀ hS1 (by omega)
      have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
        (mul_nonneg hC.le (pow_nonneg hB (2*j+s)))) (hQ j s)
      convert! hh using 1 <;>dsimp only[S,B]<;>ring
    · rw[if_neg h,map_zero,norm_zero]
      have hi:0 ≤ (if 2 ≤ 2*j+s ∧ 2*j+s ≤ K then B^(2*j+s)*
          PowerSeries.coeff (K-(2*j+s)) (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*((PowerSeries.exp ℝ)*e)) else 0):=by
        split_ifs
        · exact mul_nonneg (pow_nonneg hB _) (hQ j s)
        · exact le_rfl
      exact mul_nonneg (mul_nonneg hC.le (pow_nonneg hS0 _)) hi
  rw[separatingSeries_sum_by_card]
  simp only[map_sum]
  calc
    _ ≤ ∑j∈Finset.range (K+1),‖∑s∈Finset.range (K+1),PowerSeries.coeff K
        (if Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ K then
          ∑I∈Finset.powersetCard s (Finset.range d.length),separatingConfiguration P R z F j t d I else 0)‖:=
      norm_sum_le _ _
    _ ≤ ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),‖PowerSeries.coeff K
        (if Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s ≤ K then
          ∑I∈Finset.powersetCard s (Finset.range d.length),separatingConfiguration P R z F j t d I else 0)‖:=
      Finset.sum_le_sum (fun j hj=>norm_sum_le _ _)
    _ ≤ ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),C*S^(2*K-1)*
        (if 2 ≤ 2*j+s ∧ 2*j+s ≤ K then B^(2*j+s)*
          PowerSeries.coeff (K-(2*j+s)) (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*((PowerSeries.exp ℝ)*e)) else 0):=
      Finset.sum_le_sum (fun j hj=>Finset.sum_le_sum (fun s hs=>hterm j s))
    _ = _:=by rw[separatingMajorant_coeff];simp only[Finset.mul_sum];rfl
end WP.HigherOrder.ComplexCanonical
