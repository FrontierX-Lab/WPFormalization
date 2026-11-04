import WPFormalization.HigherOrder.CanonicalProfileMajorant
import WPFormalization.HigherOrder.ComplexCuspMajorant
/-! The three genuine scalar updates are bounded by the C,H,G components of the proved polynomial auxiliary solution. The true cusp moment operator, KdV separating sum and unit-cusp inverse descent are instantiated with the actual coefficient budgets. These are local induction steps, not a hypothesis about completed canonical bounds. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma auxiliaryLossArgument_nonnegative (b:ℕ) (U:Fin 7→WP.HigherOrder.Series)
    (hU:∀i j,0 ≤ PowerSeries.coeff j (U i)) :
    ∀j,0 ≤ PowerSeries.coeff j (auxiliarySolutionLossArgument b U) := by
  let V:=auxiliarySolutionUnit U 0
  let C:=auxiliarySolutionUnit U 3
  let A:=auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6
  have hV:=auxiliarySolutionUnit_nonnegative U hU 0
  have hC:=auxiliarySolutionUnit_nonnegative U hU 3
  have hA:∀n,0 ≤ PowerSeries.coeff n A:=by
    intro n;rw[map_add]
    exact add_nonneg (auxiliarySolutionUnit_nonnegative U hU 4 n) (auxiliarySolutionUnit_nonnegative U hU 6 n)
  have hOneA:∀n,0 ≤ PowerSeries.coeff n (1+A):=by
    intro n;rw[map_add]
    exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (hA n)
  have hp:=coefficient_nonnegative_C_X_mul (b:ℝ) (Nat.cast_nonneg b) (V^2*C*(1+A))
    (coeff_mul_nonneg (coeff_mul_nonneg (coeff_pow_nonneg hV 2) hC) hOneA)
  have heq:PowerSeries.C (b:ℝ)*PowerSeries.X*(V^2*C*(1+A))=auxiliarySolutionLossArgument b U:=by
    dsimp[V,C,A,auxiliarySolutionLossArgument]
    ring
  simpa only[heq] using hp

lemma cuspSeries_auxiliary_norm_bound (ρ K₀ A₀:ℝ) (hρ:1<ρ) (hK₀:0<K₀) (hA₀:0<A₀) :
    ∃ B M₀:ℝ,0<B ∧ 0<M₀ ∧ ∀R:ℂ→ℂ,∀z:ℂ,
      (∀d:ℕ,‖WP.Analysis.complexDilatonCoefficient R d z‖ ≤ K₀/ρ^d)→‖(kernelA R z)⁻¹‖ ≤ A₀→
      ∀b:ℕ,B ≤ (b:ℝ)→∀U:Fin 7→WP.HigherOrder.Series,
      zeroConstant U→formalFixedPoint (auxiliaryMajorantSystem b) U→
      (∀i j,0 ≤ PowerSeries.coeff j (U i))→∀M:ℝ,M₀ ≤ M→∀K:ℕ,1 ≤ K→∀F:HierarchyJet,
      (∀i:ℕ,i ≤ K→∀d:List ℕ,1 ≤ d.length→‖PowerSeries.coeff i (F.profile d)‖ ≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 2))→∀p:ℕ,1 ≤ p→
      ‖PowerSeries.coeff K (cuspSeries R z F.profile p)‖ ≤ (scalarOrderWeight M K p)^(2*K)*
        PowerSeries.coeff K (auxiliarySolutionUnit U 3) := by
  obtain ⟨B,M₀,hB,hM₀,hcusp⟩:=cuspSeries_uniform_norm_majorant ρ K₀ A₀ hρ hK₀ hA₀
  refine ⟨B,M₀,hB,hM₀,?_⟩
  intro R z hgeom hA b hb U h0 hfixed hU M hM K hK F hProfile p hp
  let V:=auxiliarySolutionUnit U 0
  let E:=auxiliarySolutionUnit U 2
  have hVeq:V=geometricMajorant:=(auxiliaryMajorant_resolvents b U h0 hfixed).1
  have hExpV:∀n,PowerSeries.coeff n (PowerSeries.exp ℝ) ≤ PowerSeries.coeff n V:=by
    intro n;rw[hVeq];exact exp_coeff_le_geometricMajorant n
  have hE:=auxiliarySolutionUnit_nonnegative U hU 2
  have hV:=auxiliarySolutionUnit_nonnegative U hU 0
  have hCompare:=coeff_mul_mono exp_coeff_nonneg hE hExpV (fun _=>le_rfl) K
  have hpCoef:=coeff_mul_nonneg hV hE K
  have hMp:0 ≤ M:=(lt_of_lt_of_le hM₀ hM).le
  have hSp:0 ≤ (scalarOrderWeight M K p)^(2*K):=by unfold scalarOrderWeight;positivity
  have hh:=hcusp R z hgeom hA M hM K F E hE hProfile p hp
  calc
    _ ≤ B*(scalarOrderWeight M K p)^(2*K)*PowerSeries.coeff K (V*E):=
      hh.trans (mul_le_mul_of_nonneg_left hCompare (mul_nonneg hB.le hSp))
    _ ≤ (b:ℝ)*(scalarOrderWeight M K p)^(2*K)*PowerSeries.coeff K (V*E):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hSp) hpCoef
    _ = _:=by rw[auxiliary_cusp_coefficient_budget b U h0 hfixed K hK];ring

lemma genusSeries_auxiliary_norm_bound (P:PsiTheory) (R:ℂ→ℂ) (z:ℂ) (F:HierarchyJet)
    (profiles:List ℕ→Series) (M:ℝ) (hM:1 ≤ M) (K:ℕ) (hK:1 ≤ K)
    (A₀ T:ℝ) (hA₀:0 ≤ A₀) (hA:‖kernelA R z‖ ≤ A₀) (hT:1 ≤ T)
    (hsmall:∀j:ℕ,∀d:List ℕ,Stable j d.length→‖smallW P R z j d‖ ≤
      Real.Gamma (complexity j d.length:ℝ)*T^(complexity j d.length))
    (b:ℕ) (hbexp:Real.exp 6 ≤ (b:ℝ)) (hbthree:3 ≤ (b:ℝ)) (hbA:2*(T*A₀) ≤ (b:ℝ))
    (U:Fin 7→WP.HigherOrder.Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (hU:∀i j,0 ≤ PowerSeries.coeff j (U i))
    (hOld:JetMajorantInvariant M (K-1) F U)
    (hProfile:∀d:List ℕ,1 ≤ d.length→‖PowerSeries.coeff K (profiles d)‖ ≤
      (profileOrderWeight M K d)^(2*K)*PowerSeries.coeff K (auxiliarySolutionUnit U 2))
    (p:ℕ) (hp:2 ≤ p) :
    ‖PowerSeries.coeff K (genusSeries P R z F profiles K p)‖ ≤ (scalarOrderWeight M K p)^(2*K)*
      PowerSeries.coeff K (auxiliarySolutionUnit U 4) := by
  let E:=auxiliarySolutionUnit U 2
  let C:=auxiliarySolutionUnit U 3
  let A:=auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6
  have hE:=auxiliarySolutionUnit_nonnegative U hU 2
  have hC:=auxiliarySolutionUnit_nonnegative U hU 3
  have hApos:∀n,0 ≤ PowerSeries.coeff n A:=by
    intro n;rw[map_add]
    exact add_nonneg (auxiliarySolutionUnit_nonnegative U hU 4 n) (auxiliarySolutionUnit_nonnegative U hU 6 n)
  have hRaw:=genusSeries_uniform_norm_majorant P R z F profiles M hM K p hp A₀ T hA₀ hA hT hsmall E C A hE hC hApos
    hProfile hOld.2.1 (fun i hi q hq=>hOld.genus_all (by linarith) hU i hi q hq)
  have hLoss:=auxiliary_genusSeparatingMajorant_bound b U h0 hfixed hU (T*A₀) (mul_nonneg (by linarith) hA₀) hbA K
  have hQZ:0 ≤ PowerSeries.coeff K (auxiliarySolutionLossArgument b U+U 1):=by
    rw[map_add]
    exact add_nonneg (auxiliaryLossArgument_nonnegative b U hU K) (hU 1 K)
  have hBudget:PowerSeries.coeff K (PowerSeries.C (Real.exp 6)*E+
      PowerSeries.C 3*genusSeparatingMajorant K (T*A₀) C A) ≤ PowerSeries.coeff K (auxiliarySolutionUnit U 4):=by
    rw[map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_C_mul,auxiliary_high_genus_coefficient_budget b U h0 hfixed K hK]
    calc
      _ ≤ Real.exp 6*PowerSeries.coeff K E+3*PowerSeries.coeff K (auxiliarySolutionLossArgument b U+U 1):=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hLoss (by norm_num))
      _ ≤ (b:ℝ)*PowerSeries.coeff K E+(b:ℝ)*PowerSeries.coeff K (auxiliarySolutionLossArgument b U+U 1):=
        add_le_add (mul_le_mul_of_nonneg_right hbexp (hE K)) (mul_le_mul_of_nonneg_right hbthree hQZ)
      _=_:=by ring
  exact hRaw.trans (mul_le_mul_of_nonneg_left hBudget (by unfold scalarOrderWeight;positivity))

lemma descendGenus_auxiliary_norm_bound (M:ℝ) (hM:1 ≤ M) (K:ℕ) (hK:1 ≤ K)
    (cusps:ℕ→Series) (next:Series) (hc0:PowerSeries.constantCoeff (cusps 1)=1)
    (b:ℕ) (hbexp:Real.exp 6 ≤ (b:ℝ)) (U:Fin 7→WP.HigherOrder.Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (hU:∀i j,0 ≤ PowerSeries.coeff j (U i))
    (hNext:∀i:ℕ,i ≤ K→‖PowerSeries.coeff i next‖ ≤
      (scalarOrderWeight M i 2)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 4))
    (hC1:∀i:ℕ,i ≤ K→‖PowerSeries.coeff i (cusps 1)‖ ≤
      (scalarOrderWeight M i 1)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 3))
    (hC3:∀i:ℕ,i ≤ K→‖PowerSeries.coeff i (cusps 3)‖ ≤
      (scalarOrderWeight M i 3)^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 3)) :
    ‖PowerSeries.coeff K (descendGenus cusps next 1)‖ ≤ (scalarOrderWeight M K 1)^(2*K)*
      PowerSeries.coeff K (auxiliarySolutionUnit U 6) := by
  let V:=auxiliarySolutionUnit U 0
  let C:=auxiliarySolutionUnit U 3
  let H:=auxiliarySolutionUnit U 4
  let W:=auxiliarySolutionUnit U 5
  have hV:=auxiliarySolutionUnit_nonnegative U hU 0
  have hC:=auxiliarySolutionUnit_nonnegative U hU 3
  have hH:=auxiliarySolutionUnit_nonnegative U hU 4
  have hW:=auxiliarySolutionUnit_nonnegative U hU 5
  have hC0:PowerSeries.constantCoeff C=1:=by
    simpa only[←PowerSeries.coeff_zero_eq_constantCoeff] using auxiliarySolutionUnit_coeff_zero U h0 3
  have hRaw:=descendGenus_one_uniform_norm_majorant M hM K cusps next H C hH hC hC0 hc0 hNext hC1 hC3
  have hWidentity:inverseUnitMajorant C=W:=(auxiliaryMajorant_resolvents b U h0 hfixed).2.1.symm
  rw[hWidentity] at hRaw
  have hVeq:V=geometricMajorant:=(auxiliaryMajorant_resolvents b U h0 hfixed).1
  have hExpV:∀n,PowerSeries.coeff n (PowerSeries.exp ℝ) ≤ PowerSeries.coeff n V:=by
    intro n;rw[hVeq];exact exp_coeff_le_geometricMajorant n
  have hComp1:∀n,PowerSeries.coeff n ((PowerSeries.exp ℝ)*H) ≤ PowerSeries.coeff n (V*H):=
    fun n=>coeff_mul_mono exp_coeff_nonneg hH hExpV (fun _=>le_rfl) n
  have hComp2:∀n,PowerSeries.coeff n ((PowerSeries.exp ℝ)*H*C) ≤ PowerSeries.coeff n (V*H*C):=
    fun n=>coeff_mul_mono (coeff_mul_nonneg exp_coeff_nonneg hH) hC hComp1 (fun _=>le_rfl) n
  have hCompare:=coeff_mul_mono (coeff_mul_nonneg (coeff_mul_nonneg exp_coeff_nonneg hH) hC) hW hComp2 (fun _=>le_rfl) K
  have hPos:=coeff_mul_nonneg (coeff_mul_nonneg (coeff_mul_nonneg hV hH) hC) hW K
  have hM0:0 ≤ M:=by linarith
  have hSp:0 ≤ (scalarOrderWeight M K 1)^(2*K):=by unfold scalarOrderWeight;positivity
  calc
    _ ≤ Real.exp 6*(scalarOrderWeight M K 1)^(2*K)*PowerSeries.coeff K (V*H*C*W):=
      hRaw.trans (mul_le_mul_of_nonneg_left hCompare (mul_nonneg (Real.exp_pos _).le hSp))
    _ ≤ (b:ℝ)*(scalarOrderWeight M K 1)^(2*K)*PowerSeries.coeff K (V*H*C*W):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbexp hSp) hPos
    _=_:=by rw[auxiliary_descent_coefficient_budget b U h0 hfixed K hK];ring
end WP.HigherOrder.ComplexCanonical
