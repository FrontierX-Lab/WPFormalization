import WPFormalization.HigherOrder.ComplexSeparatingKernelMajorant
import WPFormalization.HigherOrder.SmallComponentCounts
import WPFormalization.HigherOrder.PositiveSeriesBounds
/-! The actual complex separating configuration, summed over all label subsets of a fixed cardinality. The genuine component Gamma bound and the proved binomial/Gamma inequality give the loss-r polynomial count, uniformly in all degrees and marking counts. The displayed lower coefficient data and component estimate are local inputs to the future simultaneous hierarchy induction. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

def separatingConfiguration (P:PsiTheory) (R:ℂ→ℂ) (z:ℂ) (F:HierarchyJet)
    (j t:ℕ) (d:List ℕ) (I:Finset ℕ) : Series :=
  ratioSeries R z F (d.length+1) j I.card*
    coefficientSum (fun l:ℕ=>PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
      ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
        complexityShift (2*j+I.card)
          (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))

lemma separating_label_layer_norm_majorant (ρ K₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) :
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
        ∀j s t:ℕ,∀d:List ℕ,Stable j (s+1)→2 ≤ 2*j+s→2*j+s ≤ K→∀n:ℕ,n+(2*j+s) ≤ K→
        (∑I∈Finset.powersetCard s (Finset.range d.length),
          ‖PowerSeries.coeff (n+(2*j+s)) (separatingConfiguration P R z F j t d I)‖) ≤
          C*(T*‖kernelA R z‖)^(2*j+s)*(profileOrderWeight M K (t::d))^(2*n+(2*j+s)+1)*
            PowerSeries.coeff n (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*((PowerSeries.exp ℝ)*e)) := by
  obtain ⟨C,M₁,hC,hM₁,hterm⟩:=separating_term_norm_majorant ρ K₀ hρ hK₀
  refine ⟨C,max M₁ 1,hC,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro R z hgeom M hM K F e g a he hg ha hprofile hcusp hgenus P T hT hsmall j s t d hst hr hrK n hn
  have hMop:M₁ ≤ M:=(le_max_left _ _).trans hM
  have hM1:1 ≤ M:=(le_max_right _ _).trans hM
  have hM0:0 ≤ M:=by linarith
  let r:=2*j+s
  let S:=profileOrderWeight M K (t::d)
  let Bc:=Real.Gamma ((r-1:ℕ):ℝ)*T^(r-1)
  let Q:=PowerSeries.coeff n (((((PowerSeries.exp ℝ)^2)*g)^r*a^j)*((PowerSeries.exp ℝ)*e))
  have hGamma:0 ≤ Real.Gamma ((r-1:ℕ):ℝ):=(Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<r-1 by dsimp[r];omega))).le
  have hT0:0 ≤ T:=by linarith
  have hBc:0 ≤ Bc:=mul_nonneg hGamma (pow_nonneg hT0 _)
  have hS0:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hQ:0 ≤ Q:=by
    have hExp2:∀k,0 ≤ PowerSeries.coeff k ((PowerSeries.exp ℝ)^2):=by
      simpa only[pow_two] using coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg
    exact coeff_mul_nonneg (coeff_mul_nonneg
      (coeff_pow_nonneg (coeff_mul_nonneg hExp2 hg) r) (coeff_pow_nonneg ha j))
      (coeff_mul_nonneg exp_coeff_nonneg he) n
  have hpoint (I:Finset ℕ) (hI:I∈Finset.powersetCard s (Finset.range d.length)) :
      ‖PowerSeries.coeff (n+r) (separatingConfiguration P R z F j t d I)‖ ≤
        C*Bc*‖kernelA R z‖^r*S^(2*n+1)*Q:=by
    obtain ⟨hIs,hIc⟩:=Finset.mem_powersetCard.mp hI
    have hb:=hterm R z hgeom M hMop K F e g a he hg ha hprofile hcusp hgenus
      P j t d I hIs (by simpa only[hIc] using hr) (by simpa only[hIc] using hrK) Bc hBc (by
        intro u
        have hbs:=smallW_selected_gamma_bound P R z T hsmall j d I hIs
          (by simpa only[hIc] using hst) u
        simpa only[hIc] using hbs) n (by simpa only[hIc] using hn)
    simpa only[separatingConfiguration,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hIc] using hb
  have hcountS:((d.length+r:ℕ):ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM1 (Nat.cast_nonneg K : (0:ℝ) ≤ K)
    have hrR:(r:ℝ) ≤ K:=by exact_mod_cast hrK
    dsimp[S,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [Nat.cast_nonneg (α:=ℝ) (t::d).sum]
  have hcount:(d.length.choose s:ℝ)*Bc ≤ (T*S)^r:=by
    have hb:=small_component_label_norm_bound d.length r s (by dsimp[r];omega) (by dsimp[r];omega)
      T S hT hcountS Bc (by rw[Real.norm_eq_abs,abs_of_nonneg hBc])
    simpa only[Real.norm_eq_abs,abs_of_nonneg hBc] using hb
  calc
    _ ≤ ∑I∈Finset.powersetCard s (Finset.range d.length),C*Bc*‖kernelA R z‖^r*S^(2*n+1)*Q:=
      Finset.sum_le_sum hpoint
    _ = (d.length.choose s:ℝ)*(C*Bc*‖kernelA R z‖^r*S^(2*n+1)*Q):=by
      simp only[Finset.sum_const,Finset.card_powersetCard,Finset.card_range,nsmul_eq_mul]
    _ = (C*‖kernelA R z‖^r*S^(2*n+1)*Q)*((d.length.choose s:ℝ)*Bc):=by ring
    _ ≤ (C*‖kernelA R z‖^r*S^(2*n+1)*Q)*(T*S)^r:=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _:=by
      dsimp only[S,Q,r]
      rw[show 2*n+(2*j+s)+1=(2*n+1)+(2*j+s) by omega,pow_add,mul_pow,mul_pow]
      ring
end WP.HigherOrder.ComplexCanonical
