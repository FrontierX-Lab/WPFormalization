import WPFormalization.HigherOrder.CanonicalNormInvariant
import WPFormalization.HigherOrder.AuxiliaryCoefficientBudgets
import WPFormalization.HigherOrder.AuxiliaryLossDomination
/-! The actual complex canonical profile update is bounded by the E component of the genuine seven-component polynomial majorant solution. This instantiates the complete linear and separating operators, label counts, loss-tail domination and canonical path bound. The explicit finite-stage invariant is the local induction hypothesis, to be proved at every actual stage. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma profileAtOrder_auxiliary_norm_bound (ρ K₀ A₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) (hA₀:0<A₀) :
    ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧ ∀P:PsiTheory,∀R:ℂ→ℂ,∀z:ℂ,
      (∀l:ℕ,‖WP.Analysis.complexWeightCoeff R l z‖ ≤ K₀/ρ^l)→‖kernelA R z‖ ≤ A₀→
      ∀T:ℝ,1 ≤ T→(∀j:ℕ,∀d:List ℕ,Stable j d.length→‖smallW P R z j d‖ ≤
        Real.Gamma (complexity j d.length:ℝ)*T^(complexity j d.length))→
      ∀b:ℕ,B+2*T*A₀ ≤ (b:ℝ)→∀U:Fin 7→WP.HigherOrder.Series,
      zeroConstant U→formalFixedPoint (auxiliaryMajorantSystem b) U→
      (∀i j,0 ≤ PowerSeries.coeff j (U i))→∀M:ℝ,M₀ ≤ M→∀K:ℕ,1 ≤ K→∀F:HierarchyJet,
      JetMajorantInvariant M (K-1) F U→∀d:List ℕ,1 ≤ d.length→
      ‖profileAtOrder P R z F K d‖ ≤ (profileOrderWeight M K d)^(2*K)*
        PowerSeries.coeff K (auxiliarySolutionUnit U 2) := by
  obtain ⟨B₁,M₁,hB₁,hM₁,hlinear⟩:=linearSeries_uniform_norm_majorant ρ K₀ A₀ hρ hK₀ hA₀
  obtain ⟨B₂,M₂,hB₂,hM₂,hseparating⟩:=separatingSeries_norm_majorant ρ K₀ hρ hK₀
  refine ⟨B₁+B₂+1,max (max M₁ M₂) 1,by positivity,
    lt_of_lt_of_le hM₁ ((le_max_left M₁ M₂).trans (le_max_left _ _)),?_⟩
  intro P R z hgeom hAz T hT hsmall b hb U h0 hfixed hU M hM K hK F hI d hd
  have hM1:M₁ ≤ M:=((le_max_left _ _).trans (le_max_left _ _)).trans hM
  have hM2:M₂ ≤ M:=((le_max_right _ _).trans (le_max_left _ _)).trans hM
  have hMone:1 ≤ M:=(le_max_right _ _).trans hM
  have hMzero:0 ≤ M:=by linarith
  have hTzero:0 ≤ T:=by linarith
  have hb1:B₁ ≤ (b:ℝ):=by nlinarith[mul_nonneg hTzero hA₀.le]
  have hb2:B₂ ≤ (b:ℝ):=by nlinarith[mul_nonneg hTzero hA₀.le]
  have hbA:2*(T*‖kernelA R z‖) ≤ (b:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_left hAz hTzero
    nlinarith
  let V:=auxiliarySolutionUnit U 0
  let E:=auxiliarySolutionUnit U 2
  let C:=auxiliarySolutionUnit U 3
  let A:=auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6
  let L:=PowerSeries.coeff K (PowerSeries.X*(V^3*E*C*(1+A)))
  let Sₑ:=PowerSeries.coeff K ((V*E)*U 1)
  have hV:=auxiliarySolutionUnit_nonnegative U hU 0
  have hE:=auxiliarySolutionUnit_nonnegative U hU 2
  have hC:=auxiliarySolutionUnit_nonnegative U hU 3
  have hA:∀n,0 ≤ PowerSeries.coeff n A:=by
    intro n;rw[map_add]
    exact add_nonneg (auxiliarySolutionUnit_nonnegative U hU 4 n) (auxiliarySolutionUnit_nonnegative U hU 6 n)
  have hOneA:∀n,0 ≤ PowerSeries.coeff n (1+A):=by
    intro n;rw[map_add]
    exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (hA n)
  have hExp3:∀n,0 ≤ PowerSeries.coeff n ((PowerSeries.exp ℝ)^3):=coeff_pow_nonneg exp_coeff_nonneg 3
  have hVeq:V=geometricMajorant:=(auxiliaryMajorant_resolvents b U h0 hfixed).1
  have hExpV3:∀n,PowerSeries.coeff n ((PowerSeries.exp ℝ)^3) ≤ PowerSeries.coeff n (V^3):=by
    intro n;rw[hVeq];exact exp_pow_coeff_le_geometricMajorant 3 n
  have hLinCoef (n:ℕ) : PowerSeries.coeff n (((PowerSeries.exp ℝ)^3)*C*(1+A)*E) ≤
      PowerSeries.coeff n (V^3*E*C*(1+A)):=by
    have hbc:∀m,PowerSeries.coeff m (((PowerSeries.exp ℝ)^3)*C) ≤ PowerSeries.coeff m (V^3*C):=
      fun m=>coeff_mul_mono hExp3 hC hExpV3 (fun _=>le_rfl) m
    have hbca:∀m,PowerSeries.coeff m (((PowerSeries.exp ℝ)^3)*C*(1+A)) ≤ PowerSeries.coeff m (V^3*C*(1+A)):=
      fun m=>coeff_mul_mono (coeff_mul_nonneg hExp3 hC) hOneA hbc (fun _=>le_rfl) m
    have hh:=coeff_mul_mono (coeff_mul_nonneg (coeff_mul_nonneg hExp3 hC) hOneA) hE hbca (fun _=>le_rfl) n
    have heq:V^3*C*(1+A)*E=V^3*E*C*(1+A):=by ring
    exact hh.trans_eq (congrArg (PowerSeries.coeff n) heq)
  have hLzero:0 ≤ L:=by
    have hX:∀n,0 ≤ PowerSeries.coeff n (PowerSeries.X:WP.HigherOrder.Series):=by
      intro n;rw[PowerSeries.coeff_X];split_ifs<;>norm_num
    exact coeff_mul_nonneg hX (coeff_mul_nonneg
      (coeff_mul_nonneg (coeff_mul_nonneg (coeff_pow_nonneg hV 3) hE) hC) hOneA) K
  have hSezero:0 ≤ Sₑ:=coeff_mul_nonneg (coeff_mul_nonneg hV hE) (hU 1) K
  have hbudget:B₁*L+B₂*Sₑ ≤ PowerSeries.coeff K E:=by
    have he:=auxiliary_profile_coefficient_budget b U h0 hfixed K hK
    change PowerSeries.coeff K E=(b:ℝ)*(L+Sₑ) at he
    rw[he]
    calc B₁*L+B₂*Sₑ ≤ (b:ℝ)*L+(b:ℝ)*Sₑ:=
      add_le_add (mul_le_mul_of_nonneg_right hb1 hLzero) (mul_le_mul_of_nonneg_right hb2 hSezero)
      _=_:=by ring
  have hgenus:∀i:ℕ,i ≤ K-1→∀p:ℕ,1 ≤ p→‖PowerSeries.coeff i (F.genus p)‖ ≤
      (scalarOrderWeight M i p)^(2*i)*PowerSeries.coeff i A:=
    fun i hi p hp=>hI.genus_all hMzero hU i hi p hp
  apply profileAtOrder_norm_bound_of_adjacent P R z F M hMzero K hK
    (PowerSeries.coeff K E) (hE K) _ d hd
  intro v hv i hi
  let S:=profileOrderWeight M K v
  have hSzero:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hl:=hlinear R z hgeom hAz M hM1 (K-1) F E C A hE hC hA hI.1 hI.2.1 hgenus (v[i]!) (v.eraseIdx i)
  rw[Nat.sub_add_cancel hK,coordinate_parent_order_weight M K v i hi] at hl
  rw[show 2*(K-1)+1=2*K-1 by omega] at hl
  have hx:PowerSeries.coeff K (PowerSeries.X*(V^3*E*C*(1+A)))=
      PowerSeries.coeff (K-1) (V^3*E*C*(1+A)):=by
    simpa only[pow_one,Nat.sub_add_cancel hK] using PowerSeries.coeff_X_pow_mul (V^3*E*C*(1+A)) 1 (K-1)
  have hlcoef:PowerSeries.coeff (K-1) (((PowerSeries.exp ℝ)^3)*C*(1+A)*E) ≤ L:=
    (hLinCoef (K-1)).trans_eq hx.symm
  have hl':‖PowerSeries.coeff K (mergerSeries R z F (v[i]!) (v.eraseIdx i)+nonseparatingSeries R z F (v[i]!) (v.eraseIdx i))‖ ≤
      B₁*S^(2*K-1)*L:=hl.trans (mul_le_mul_of_nonneg_left hlcoef (mul_nonneg hB₁.le (pow_nonneg hSzero _)))
  have hs:=hseparating R z hgeom M hM2 K F E C A hE hC hA hI.1 hI.2.1 hgenus P T hT hsmall (v[i]!) (v.eraseIdx i)
  rw[coordinate_parent_order_weight M K v i hi] at hs
  have hLoss:=auxiliary_separatingMajorant_bound b U h0 hfixed hU (T*‖kernelA R z‖)
    (mul_nonneg hTzero (norm_nonneg _)) hbA K
  have hs':‖PowerSeries.coeff K (separatingSeries P R z F K (v[i]!) (v.eraseIdx i))‖ ≤
      B₂*S^(2*K-1)*Sₑ:=hs.trans (mul_le_mul_of_nonneg_left hLoss (mul_nonneg hB₂.le (pow_nonneg hSzero _)))
  dsimp only[adjacentCoefficient]
  rw[norm_neg,map_add]
  calc
    _ ≤ ‖PowerSeries.coeff K (mergerSeries R z F (v[i]!) (v.eraseIdx i)+nonseparatingSeries R z F (v[i]!) (v.eraseIdx i))‖+
        ‖PowerSeries.coeff K (separatingSeries P R z F K (v[i]!) (v.eraseIdx i))‖:=norm_add_le _ _
    _ ≤ B₁*S^(2*K-1)*L+B₂*S^(2*K-1)*Sₑ:=add_le_add hl' hs'
    _=S^(2*K-1)*(B₁*L+B₂*Sₑ):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left hbudget (pow_nonneg hSzero _)
end WP.HigherOrder.ComplexCanonical
