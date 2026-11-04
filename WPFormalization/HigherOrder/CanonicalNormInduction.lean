import WPFormalization.HigherOrder.CanonicalScalarMajorant
/-! The actual nextJet preserves the normalized majorant invariant: the profile is updated first, then the cusp, high genus and genuine p=1 inverse-cusp descent. Prefix coefficients are preserved by the exact setCoeff definitions. Induction proves the invariant at every actual hierarchyJet, with the common local kernel/component data and the independently constructed polynomial auxiliary solution. No canonical coefficient bound is assumed. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma nextJet_auxiliary_norm_invariant (ρ K₀ A₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) (hA₀:0<A₀) :
    ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧ ∀P:PsiTheory,∀R:ℂ→ℂ,∀z:ℂ,
      (∀l:ℕ,‖WP.Analysis.complexWeightCoeff R l z‖ ≤ K₀/ρ^l)→
      (∀l:ℕ,‖WP.Analysis.complexDilatonCoefficient R l z‖ ≤ K₀/ρ^l)→
      ‖kernelA R z‖ ≤ A₀→‖(kernelA R z)⁻¹‖ ≤ A₀→
      ∀T:ℝ,1 ≤ T→(∀j:ℕ,∀d:List ℕ,Stable j d.length→‖smallW P R z j d‖ ≤
        Real.Gamma (complexity j d.length:ℝ)*T^(complexity j d.length))→
      ∀b:ℕ,B+2*T*A₀ ≤ (b:ℝ)→∀U:Fin 7→WP.HigherOrder.Series,
      zeroConstant U→formalFixedPoint (auxiliaryMajorantSystem b) U→
      (∀i j,0 ≤ PowerSeries.coeff j (U i))→∀M:ℝ,M₀ ≤ M→∀K:ℕ,1 ≤ K→∀F:HierarchyJet,
      PowerSeries.constantCoeff (F.cusp 1)=1→JetMajorantInvariant M (K-1) F U→
      JetMajorantInvariant M K (nextJet P R z K F) U := by
  obtain ⟨B₁,M₁,hB₁,hM₁,hprofile⟩:=profileAtOrder_auxiliary_norm_bound ρ K₀ A₀ hρ hK₀ hA₀
  obtain ⟨B₂,M₂,hB₂,hM₂,hcusp⟩:=cuspSeries_auxiliary_norm_bound ρ K₀ A₀ hρ hK₀ hA₀
  refine ⟨B₁+B₂+Real.exp 6+4,max (max M₁ M₂) 1,by positivity,
    lt_of_lt_of_le hM₁ ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro P R z hW hB hA hAi T hT hsmall b hb U h0 hfixed hU M hM K hK F hFc0 hOld
  have hM1:M₁ ≤ M:=((le_max_left _ _).trans (le_max_left _ _)).trans hM
  have hM2:M₂ ≤ M:=((le_max_right _ _).trans (le_max_left _ _)).trans hM
  have hMone:1 ≤ M:=(le_max_right _ _).trans hM
  have hTA:0 ≤ T*A₀:=mul_nonneg (by linarith) hA₀.le
  have hb1:B₁+2*T*A₀ ≤ (b:ℝ):=by linarith[Real.exp_pos 6]
  have hb2:B₂ ≤ (b:ℝ):=by linarith[Real.exp_pos 6]
  have hbexp:Real.exp 6 ≤ (b:ℝ):=by linarith
  have hbthree:3 ≤ (b:ℝ):=by linarith[Real.exp_pos 6]
  have hbA:2*(T*A₀) ≤ (b:ℝ):=by linarith[Real.exp_pos 6]
  let profiles:=fun d=>setCoeff (F.profile d) K (profileAtOrder P R z F K d)
  let cusps:=fun p=>setCoeff (F.cusp p) K (PowerSeries.coeff K (cuspSeries R z profiles p))
  let highGenus:=fun p=>setCoeff (F.genus p) K (PowerSeries.coeff K (genusSeries P R z F profiles K p))
  have hProfileCurrent (d:List ℕ) (hd:1 ≤ d.length) :
      ‖profileAtOrder P R z F K d‖ ≤ (profileOrderWeight M K d)^(2*K)*
        PowerSeries.coeff K (auxiliarySolutionUnit U 2):=
    hprofile P R z hW hA T hT hsmall b hb1 U h0 hfixed hU M hM1 K hK F hOld d hd
  have hProfiles:∀i:ℕ,i ≤ K→∀d:List ℕ,1 ≤ d.length→‖PowerSeries.coeff i (profiles d)‖ ≤
      (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 2):=by
    intro i hi d hd
    by_cases hik:i=K
    · subst i
      simpa only[profiles,setCoeff,PowerSeries.coeff_mk,if_pos rfl,ite_true] using hProfileCurrent d hd
    · simp only[profiles,setCoeff,PowerSeries.coeff_mk,if_neg hik]
      exact hOld.1 i (by omega) d hd
  have hCuspCurrent (p:ℕ) (hp:1 ≤ p) :
      ‖PowerSeries.coeff K (cuspSeries R z profiles p)‖ ≤ (scalarOrderWeight M K p)^(2*K)*
        PowerSeries.coeff K (auxiliarySolutionUnit U 3):=
    hcusp R z hB hAi b hb2 U h0 hfixed hU M hM2 K hK ⟨profiles,F.cusp,F.genus⟩ hProfiles p hp
  have hCusps:∀i:ℕ,i ≤ K→∀p:ℕ,1 ≤ p→‖PowerSeries.coeff i (cusps p)‖ ≤
      (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 3):=by
    intro i hi p hp
    by_cases hik:i=K
    · subst i
      simpa only[cusps,setCoeff,PowerSeries.coeff_mk,if_pos rfl,ite_true] using hCuspCurrent p hp
    · simp only[cusps,setCoeff,PowerSeries.coeff_mk,if_neg hik]
      exact hOld.2.1 i (by omega) p hp
  have hHighCurrent (p:ℕ) (hp:2 ≤ p) :
      ‖PowerSeries.coeff K (genusSeries P R z F profiles K p)‖ ≤ (scalarOrderWeight M K p)^(2*K)*
        PowerSeries.coeff K (auxiliarySolutionUnit U 4):=
    genusSeries_auxiliary_norm_bound P R z F profiles M hMone K hK A₀ T hA₀.le hA hT hsmall
      b hbexp hbthree hbA U h0 hfixed hU hOld (fun d hd=>hProfiles K le_rfl d hd) p hp
  have hNext:∀i:ℕ,i ≤ K→‖PowerSeries.coeff i (highGenus 2)‖ ≤
      (scalarOrderWeight M i 2)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 4):=by
    intro i hi
    by_cases hik:i=K
    · subst i
      simpa only[highGenus,setCoeff,PowerSeries.coeff_mk,if_pos rfl,ite_true] using hHighCurrent 2 (by norm_num)
    · simp only[highGenus,setCoeff,PowerSeries.coeff_mk,if_neg hik]
      exact hOld.2.2.1 i (by omega) 2 (by norm_num)
  have hc0:PowerSeries.constantCoeff (cusps 1)=1:=by
    dsimp only[cusps]
    rw[setCoeff_constant _ _ _ (by omega),hFc0]
  have hOneCurrent:=descendGenus_auxiliary_norm_bound M hMone K hK cusps (highGenus 2) hc0
    b hbexp U h0 hfixed hU hNext (fun i hi=>hCusps i hi 1 (by norm_num)) (fun i hi=>hCusps i hi 3 (by norm_num))
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi d hd
    by_cases hik:i=K
    · subst i
      change ‖PowerSeries.coeff K (profiles d)‖ ≤ _
      exact hProfiles K le_rfl d hd
    · rw[(nextJet_coeff_below P R z K F i (by omega)).1 d]
      exact hOld.1 i (by omega) d hd
  · intro i hi p hp
    by_cases hik:i=K
    · subst i
      change ‖PowerSeries.coeff K (cusps p)‖ ≤ _
      exact hCusps K le_rfl p hp
    · rw[(nextJet_coeff_below P R z K F i (by omega)).2.1 p]
      exact hOld.2.1 i (by omega) p hp
  · intro i hi p hp
    by_cases hik:i=K
    · subst i
      have hp0:p≠0:=by omega
      have hp1:p≠1:=by omega
      change ‖PowerSeries.coeff K (if p=0 then _ else if p=1 then _ else highGenus p)‖ ≤ _
      rw[if_neg hp0,if_neg hp1]
      simpa only[highGenus,setCoeff,PowerSeries.coeff_mk,if_pos rfl,ite_true] using hHighCurrent p hp
    · rw[(nextJet_coeff_below P R z K F i (by omega)).2.2 p]
      exact hOld.2.2.1 i (by omega) p hp
  · intro i hi
    by_cases hik:i=K
    · subst i
      change ‖PowerSeries.coeff K (setCoeff (F.genus 1) K
        (PowerSeries.coeff K (descendGenus cusps (highGenus 2) 1)))‖ ≤ _
      simpa only[setCoeff,PowerSeries.coeff_mk,if_pos rfl,ite_true] using hOneCurrent
    · rw[(nextJet_coeff_below P R z K F i (by omega)).2.2 1]
      exact hOld.2.2.2 i (by omega)
lemma hierarchyJet_auxiliary_norm_invariant (ρ K₀ A₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) (hA₀:0<A₀) :
    ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧ ∀P:PsiTheory,∀R:ℂ→ℂ,∀z:ℂ,
      (∀l:ℕ,‖WP.Analysis.complexWeightCoeff R l z‖ ≤ K₀/ρ^l)→
      (∀l:ℕ,‖WP.Analysis.complexDilatonCoefficient R l z‖ ≤ K₀/ρ^l)→
      ‖kernelA R z‖ ≤ A₀→‖(kernelA R z)⁻¹‖ ≤ A₀→
      ∀T:ℝ,1 ≤ T→(∀j:ℕ,∀d:List ℕ,Stable j d.length→‖smallW P R z j d‖ ≤
        Real.Gamma (complexity j d.length:ℝ)*T^(complexity j d.length))→
      ∀b:ℕ,B+2*T*A₀ ≤ (b:ℝ)→∀U:Fin 7→WP.HigherOrder.Series,
      zeroConstant U→formalFixedPoint (auxiliaryMajorantSystem b) U→
      (∀i j,0 ≤ PowerSeries.coeff j (U i))→∀M:ℝ,M₀ ≤ M→∀N:ℕ,
      JetMajorantInvariant M N (hierarchyJet P R z N) U := by
  obtain ⟨B,M₀,hB,hM₀,hStep⟩:=nextJet_auxiliary_norm_invariant ρ K₀ A₀ hρ hK₀ hA₀
  refine ⟨B,M₀,hB,hM₀,?_⟩
  intro P R z hW hBg hA hAi T hT hsmall b hb U h0 hfixed hU M hM N
  induction N with
  | zero=>simpa only[hierarchyJet] using baseJet_majorant_invariant M U h0
  | succ N ih=>
    change JetMajorantInvariant M (N+1) (nextJet P R z (N+1) (hierarchyJet P R z N)) U
    apply hStep P R z hW hBg hA hAi T hT hsmall b hb U h0 hfixed hU M hM (N+1) (by omega)
      (hierarchyJet P R z N)
    · exact (hierarchy_unit_constants P R z N).2.1 1
    · simpa only[Nat.add_sub_cancel] using ih
end WP.HigherOrder.ComplexCanonical
