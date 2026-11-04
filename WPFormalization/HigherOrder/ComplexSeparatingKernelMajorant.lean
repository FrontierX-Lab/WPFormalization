import WPFormalization.HigherOrder.ComplexLinearMajorant
import WPFormalization.HigherOrder.ComplexRatioMajorant
set_option maxHeartbeats 800000
/-! Actual complex separating kernel summability and loss-r configuration norm bounds from displayed lower-order data. The finite ratio is the original ratioSeries, and the bounded component is the genuine smallW. Common-domain Gamma data can be applied via smallW_selected_gamma_bound. No complete hierarchy or separating label-sum bound is assumed. -/
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries
lemma separating_kernel_norm_majorant (ρ K₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) :
    ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧ ∀R:ℂ→ℂ,∀z:ℂ,
      (∀l:ℕ,‖WP.Analysis.complexWeightCoeff R l z‖ ≤ K₀/ρ^l)→
      ∀M:ℝ,M₀ ≤ M→∀K:ℕ,∀F:HierarchyJet,∀e:WP.HigherOrder.Series,
      (∀n:ℕ,0 ≤ PowerSeries.coeff n e)→
      (∀i:ℕ,i ≤ K-1→∀d:List ℕ,1 ≤ d.length→‖PowerSeries.coeff i (F.profile d)‖ ≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)→
      ∀P:PsiTheory,∀j t:ℕ,∀d:List ℕ,∀I:Finset ℕ,
        2 ≤ 2*j+I.card→2*j+I.card ≤ K→∀B:ℝ,0 ≤ B→
        (∀u:ℕ,‖smallW P R z j (u::selectedNat d I)‖ ≤ B)→∀n:ℕ,n+(2*j+I.card) ≤ K→
        Summable (fun l:ℕ=>WP.Analysis.complexWeightCoeff R l z*PowerSeries.coeff n
          (∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
            complexityShift ((2*j+I.card:ℕ):ℂ) (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))) ∧
        ‖PowerSeries.coeff n (coefficientSum (fun l:ℕ=>PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
          ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
            complexityShift ((2*j+I.card:ℕ):ℂ) (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))))‖ ≤
          C*B*(profileOrderWeight M K (t::d))^(2*n+1)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e) := by
  obtain ⟨C,M₁,hC,hM₁,hkernel⟩:=geometric_coefficient_tsum_order_bounds (𝕜:=ℂ) ρ K₀ hρ hK₀
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro R z hgeom M hM K F e he hprofile P j t d I hr hrK B hB hsmall n hn
  have hMop:M₁ ≤ M:=(le_max_left _ _).trans hM
  have hM1:1 ≤ M:=(le_max_right _ _).trans hM
  have hM0:0 ≤ M:=by linarith
  let r:=2*j+I.card
  let S:=profileOrderWeight M K (t::d)
  have hKS:(K:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM1 (Nat.cast_nonneg K : (0:ℝ) ≤ K)
    dsimp[S,profileOrderWeight]
    linarith [Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) (t::d).length]
  have hEN:=coeff_mul_nonneg exp_coeff_nonneg he
  let L:ℕ→Series:=fun l=>∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
    complexityShift r (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
  have hL (l:ℕ) : ‖PowerSeries.coeff n (L l)‖ ≤
      (B*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e))*(S+l+1)^(2*n+1):=by
    have hSl:(K:ℝ) ≤ S+l+1:=by linarith[Nat.cast_nonneg (α:=ℝ) l]
    have hSl0:0 ≤ S+l+1:=(Nat.cast_nonneg K).trans hSl
    have hpoint (u:ℕ) (hu:u∈Finset.range (t+l-1)) :
        ‖PowerSeries.coeff n (PowerSeries.C (smallW P R z j (u::selectedNat d I))*
          complexityShift r (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))‖ ≤
        B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)):=by
      have hnorm:‖(r:ℂ)‖ ≤ (K:ℝ):=by rw[Complex.norm_natCast];exact_mod_cast hrK
      have hshift:=complex_shift_coeff_exponential_majorant (r:ℂ) (S+l+1)
        (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
        (fun i=>PowerSeries.coeff i e) n K (by omega) hnorm hSl he (by
          intro i hi
          have hp:=hprofile i (by omega) ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) (by simp)
          have hw:=separating_order_weight M hM0 i K t l u d ((Finset.range d.length)\I)
            (by omega) (Finset.mem_range.mp hu)
          have hw0:0 ≤ profileOrderWeight M i ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)):=by
            unfold profileOrderWeight;positivity
          have hw':profileOrderWeight M i ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) ≤ S+l+1:=by
            dsimp[S];linarith
          simpa only[mul_comm] using hp.trans
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw' _) (he i)))
      have hmk:PowerSeries.mk (fun i=>PowerSeries.coeff i e)=e:=by ext i;simp
      rw[hmk] at hshift
      rw[PowerSeries.coeff_C_mul,norm_mul]
      exact mul_le_mul (hsmall u) (by simpa only[complexityShift,shiftVariable] using hshift)
        (norm_nonneg _) hB
    simp only[L,map_sum]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑u∈Finset.range (t+l-1),B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)):=
        Finset.sum_le_sum hpoint
      _=((t+l-1:ℕ):ℝ)*(B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e))):=by
        simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      _ ≤ (S+l+1)*(B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e))):=
        mul_le_mul_of_nonneg_right
          ((pair_count_le_order_weight M hM0 K t l d).trans (by dsimp[S];linarith))
          (mul_nonneg hB (mul_nonneg (pow_nonneg hSl0 _) (hEN n)))
      _=_:=by rw[pow_succ];ring
  have hop:=hkernel M hMop (fun l=>WP.Analysis.complexWeightCoeff R l z) hgeom
    K (t::d).sum (t::d).length (2*n+1) n (by simp) (by omega)
    _ (mul_nonneg hB (hEN n)) L hL
  refine ⟨hop.1,?_⟩
  simp only[coefficientSum,PowerSeries.coeff_mk,PowerSeries.coeff_C_mul]
  convert! hop.2 using 1 <;>dsimp[S,profileOrderWeight,L,r]<;>ring
lemma separating_term_norm_majorant (ρ K₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) :
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
      ∀P:PsiTheory,∀j t:ℕ,∀d:List ℕ,∀I:Finset ℕ,I⊆Finset.range d.length→
        2 ≤ 2*j+I.card→2*j+I.card ≤ K→∀B:ℝ,0 ≤ B→
        (∀u:ℕ,‖smallW P R z j (u::selectedNat d I)‖ ≤ B)→∀n:ℕ,n+(2*j+I.card) ≤ K→
        ‖PowerSeries.coeff (n+(2*j+I.card)) (ratioSeries R z F (d.length+1) j I.card*
          coefficientSum (fun l:ℕ=>PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
            ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
              complexityShift ((2*j+I.card:ℕ):ℂ)
                (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))))‖ ≤
          C*B*‖kernelA R z‖^(2*j+I.card)*(profileOrderWeight M K (t::d))^(2*n+1)*
            PowerSeries.coeff n (((((PowerSeries.exp ℝ)^2)*g)^(2*j+I.card)*a^j)*((PowerSeries.exp ℝ)*e)) := by
  obtain ⟨C,M₁,hC,hM₁,hkernel⟩:=separating_kernel_norm_majorant ρ K₀ hρ hK₀
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro R z hgeom M hM K F e g a he hg ha hprofile hcusp hgenus P j t d I hI hr hrK B hB hsmall n hn
  have hMop:M₁ ≤ M:=(le_max_left _ _).trans hM
  have hM1:1 ≤ M:=(le_max_right _ _).trans hM
  have hM0:0 ≤ M:=by linarith
  let r:=2*j+I.card
  let S:=profileOrderWeight M K (t::d)
  have hKS:(K:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM1 (Nat.cast_nonneg K : (0:ℝ) ≤ K)
    dsimp[S,profileOrderWeight]
    linarith [Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) (t::d).length]
  have hS0:0 ≤ S:=(Nat.cast_nonneg K).trans hKS
  have hbase:scalarOrderWeight M K (d.length+1) ≤ S:=by
    dsimp[S,profileOrderWeight,scalarOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [Nat.cast_nonneg (α:=ℝ) (t::d).sum]
  have hcard:I.card ≤ d.length:=by simpa only[Finset.card_range] using Finset.card_le_card hI
  have hscalar (f:ℕ→Series) (G:WP.HigherOrder.Series) (hG:∀k,0 ≤ PowerSeries.coeff k G)
      (hf:∀i:ℕ,i ≤ K-1→∀q:ℕ,1 ≤ q→‖PowerSeries.coeff i (f q)‖ ≤
        (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i G)
      (q:ℕ) (hq:1 ≤ q) (hqr:q ≤ d.length+1+r) (i:ℕ) (hi:i ≤ n) :
      ‖PowerSeries.coeff i (f q)‖ ≤ S^(2*i)*PowerSeries.coeff i G:=by
    have hscale:scalarOrderWeight M i q ≤ S:=
      (scalar_order_weight_shift M hM1 i K (d.length+1) q r hqr (by dsimp[r];omega)).trans hbase
    have hs0:0 ≤ scalarOrderWeight M i q:=by unfold scalarOrderWeight;positivity
    exact (hf i (by omega) q hq).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hscale _) (hG i))
  let H:Series:=coefficientSum (fun l:ℕ=>PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
    ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
      complexityShift (r:ℂ) (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))
  let E:WP.HigherOrder.Series:=(PowerSeries.exp ℝ)*e
  let Q:WP.HigherOrder.Series:=PowerSeries.C (C*B*S)*E
  have hE:=coeff_mul_nonneg exp_coeff_nonneg he
  have hQ:∀k,0 ≤ PowerSeries.coeff k Q:=by
    intro k
    simp only[Q,PowerSeries.coeff_C_mul]
    exact mul_nonneg (by positivity) (hE k)
  have hH (i:ℕ) (hi:i ≤ n) : ‖PowerSeries.coeff i H‖ ≤ S^(2*i)*PowerSeries.coeff i Q:=by
    have hb:=(hkernel R z hgeom M hMop K F e he hprofile P j t d I hr hrK B hB hsmall i (by omega)).2
    dsimp only[Q]
    rw[PowerSeries.coeff_C_mul]
    convert! hb using 1 <;>dsimp only[H,E,S,r]<;>rw[pow_succ]<;>ring
  have hh:=ratioSeries_mul_norm_coeff_bound R z F (d.length+1) j I.card n K S (by omega) hn hKS
    g a Q H hg ha hQ (by
      intro b hb i hi
      have hb':b<r:=Finset.mem_range.mp hb
      apply hscalar F.cusp g hg hcusp (d.length+1-I.card+b) (by omega) (by omega) i hi) (by
      intro b hb i hi
      have hb':b<j:=Finset.mem_range.mp hb
      apply hscalar F.genus a ha hgenus (d.length+1+2*b) (by omega) (by dsimp[r];omega) i hi) hH
  have hmaj : (((PowerSeries.exp ℝ)^2*g)^r*a^j)*Q=
      PowerSeries.C (C*B*S)*((((PowerSeries.exp ℝ)^2*g)^r*a^j)*E):=by dsimp[Q];ring
  rw[hmaj,PowerSeries.coeff_C_mul] at hh
  convert! hh using 1 <;>dsimp only[H,E,S,r]<;>rw[pow_succ]<;>ring
lemma selectedNat_length_eq_card (d:List ℕ) (I:Finset ℕ) (hI:I⊆Finset.range d.length) :
    (selectedNat d I).length=I.card := by
  rw[←selectedNat_toNat,List.length_map]
  exact selected_length_card (d.map Int.ofNat) I (by simpa only[List.length_map] using hI)

lemma smallW_selected_gamma_bound (P:PsiTheory) (R:ℂ→ℂ) (z:ℂ) (T:ℝ)
    (hsmall:∀g:ℕ,∀d:List ℕ,Stable g d.length→
      ‖smallW P R z g d‖ ≤ Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (j:ℕ) (d:List ℕ) (I:Finset ℕ) (hI:I⊆Finset.range d.length)
    (hst:Stable j (I.card+1)) (u:ℕ) :
    ‖smallW P R z j (u::selectedNat d I)‖ ≤
      Real.Gamma ((2*j+I.card-1:ℕ):ℝ)*T^(2*j+I.card-1) := by
  have hlen:(u::selectedNat d I).length=I.card+1:=by
    simp only[List.length_cons,selectedNat_length_eq_card d I hI]
  have hc:complexity j (u::selectedNat d I).length=2*j+I.card-1:=by rw[hlen];unfold complexity;omega
  simpa only[hc] using hsmall j (u::selectedNat d I) (by simpa only[hlen] using hst)

end WP.HigherOrder.ComplexCanonical
