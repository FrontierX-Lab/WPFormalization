import WPFormalization.HigherOrder.CoefficientBoundsProof
import WPFormalization.HigherOrder.ComplexInverseMajorant
import WPFormalization.HigherOrder.HierarchyIdentities
/-! Uniform coefficient bounds for the actual canonical inverse cusp.
The existing seven-component norm induction supplies the true cusp component;
the proved finite inverse estimate identifies its majorant with the genuine
W component of that polynomial system. Constants precede every M>=M0,
marking count, order and closed physical parameter. No actual-remainder
bound or additional inverse-majorant premise is assumed. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries Set
lemma canonical_inverseCusp_coefficient_budget (P:PsiTheory)(R:ℂ→ℂ)(z:ℂ)
    (M:ℝ)(hM:0≤M)(b:ℕ)(U:Fin 7→WP.HigherOrder.Series)(h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U)(hU:∀i j,0≤PowerSeries.coeff j (U i))
    (p j:ℕ)(hp:1≤p)
    (hc:∀i≤j,‖cuspCoefficient P R z p i‖≤ scalarOrderWeight M i p^(2*i)*
      PowerSeries.coeff i (auxiliarySolutionUnit U 3)):
    ‖PowerSeries.coeff j ((formalCusp P R z p)⁻¹)‖≤ scalarOrderWeight M j p^(2*j)*
      PowerSeries.coeff j (auxiliarySolutionUnit U 5):=by
  let S:ℝ:=scalarOrderWeight M j p
  have hS:0≤ S:=by dsimp[S,scalarOrderWeight];positivity
  have hg0:PowerSeries.constantCoeff (auxiliarySolutionUnit U 3)=1:=by
    simpa only[PowerSeries.coeff_zero_eq_constantCoeff] using auxiliarySolutionUnit_coeff_zero U h0 3
  have hcap:∀i≤j,‖PowerSeries.coeff i (formalCusp P R z p)‖≤ S^(2*i)*
      PowerSeries.coeff i (auxiliarySolutionUnit U 3):=by
    intro i hi
    have hh:=hc i hi
    have hweight:scalarOrderWeight M i p≤ S:=by
      dsimp[S,scalarOrderWeight]
      have hiR:(i:ℝ)≤(j:ℝ):=by exact_mod_cast hi
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hiR hM)
    have hweight0:0≤ scalarOrderWeight M i p:=by unfold scalarOrderWeight;positivity
    simp only[formalCusp,PowerSeries.coeff_mk]
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hweight0 hweight _)
      (auxiliarySolutionUnit_nonnegative U hU 3 i)
  have he:=scaled_coeff_unit_inverse_bound (formalCusp P R z p) (auxiliarySolutionUnit U 3) S hS
    (by simp) hg0 (auxiliarySolutionUnit_nonnegative U hU 3) j hcap
  have hW:inverseUnitMajorant (auxiliarySolutionUnit U 3)=auxiliarySolutionUnit U 5:=
    (auxiliaryMajorant_resolvents b U h0 hfixed).2.1.symm
  rwa[hW] at he
end WP.HigherOrder.ComplexCanonical
namespace WP.HigherOrder
open PowerSeries Set
lemma inverseCusp_coefficient_uniform_bound (P:PsiTheory):
    ∃C B M₀:ℝ,0<C ∧ 0<B ∧ 2≤M₀ ∧ ∀M:ℝ,M₀≤M→∀p j:ℕ,1≤p→∀Y∈Icc (0:ℝ) y₀,
      |PowerSeries.coeff j ((formalCusp P Y p)⁻¹)|≤C*B^j*scalarOrderWeight M j p^(2*j):=by
  obtain ⟨Ω,R,ρ,C₀,A₀,hΩ,hΩv,hcover,hρ,hC₀,hA₀,hR,hunit,hraw,hR0,hR',hA,hAb,hcoef,hbound,hcrit,hmom,hsmallA,hsmallB,hphysical⟩:=
    ComplexCanonical.common_complex_canonical_inputs
  obtain ⟨T,hT,hsmall⟩:=hsmallB P
  obtain ⟨B₀,M₀,hB₀,hM₀,hInv⟩:=ComplexCanonical.hierarchyJet_auxiliary_norm_invariant ρ C₀ A₀ hρ hC₀ hA₀
  let b:ℕ:=⌈B₀+2*T*A₀⌉₊
  have hb:B₀+2*T*A₀≤(b:ℝ):=Nat.le_ceil _
  obtain ⟨U,h0,hfixed,hU,C₁,B₁,hC₁,hB₁,hgeometric⟩:=auxiliaryMajorantSolution_exists b
  let B:ℝ:=max B₁ 1
  have hB:0<B:=lt_of_lt_of_le hB₁ (le_max_left _ _)
  have hB1:1≤B:=le_max_right _ _
  have hUnits(i:Fin 7)(j:ℕ):PowerSeries.coeff j (auxiliarySolutionUnit U i)≤(C₁+1)*B^j:=by
    rw[auxiliarySolutionUnit,map_add]
    have hOne:PowerSeries.coeff j (1:Series)≤1:=by rw[PowerSeries.coeff_one];split_ifs<;>norm_num
    have hPow:B₁^j≤B^j:=pow_le_pow_left₀ hB₁.le (le_max_left _ _) j
    have hOnePow:1≤B^j:=one_le_pow₀ hB1
    calc
      _ ≤ 1+C₁*B^j:=add_le_add hOne ((hgeometric i j).trans (mul_le_mul_of_nonneg_left hPow hC₁.le))
      _ ≤ _:=by nlinarith
  refine ⟨C₁+1,B,max M₀ 2,by positivity,hB,le_max_right _ _,?_⟩
  intro M hM p j hp Y hY
  have hMbig:M₀≤M:=(le_max_left _ _).trans hM
  have hM2:2≤M:=(le_max_right _ _).trans hM
  have hz:(Y:ℂ)∈Ω:=hcover Y hY
  have hI:=hInv P R (Y:ℂ) (fun l=>(hbound _ hz l).2.1) (fun l=>(hbound _ hz l).2.2)
    (hAb _ hz).2.1 (hAb _ hz).2.2 T hT (fun g d hs=>hsmall g d hs (Y:ℂ) hz)
    b hb U h0 hfixed hU M hMbig j
  have hc:∀i≤j,‖ComplexCanonical.cuspCoefficient P R (Y:ℂ) p i‖≤
      scalarOrderWeight M i p^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 3):=by
    intro i hi
    have he:=hI.2.1 i hi p hp
    rw[ComplexCanonical.hierarchy_cusp_stable P R (Y:ℂ) p j i hi] at he
    exact he
  have he:=ComplexCanonical.canonical_inverseCusp_coefficient_budget P R (Y:ℂ) M (by linarith)
    b U h0 hfixed hU p j hp hc
  have hr:= (ComplexCanonical.canonical_formal_series_restrict_closed Ω hΩ hcover R hR hR0 hraw
    (fun z hz=>(hunit z hz).1) P Y hY).2.1 p
  rw[hr,←ComplexCanonical.ofRealSeries_inv,ComplexCanonical.ofRealSeries_coeff,
    Complex.norm_real,Real.norm_eq_abs] at he
  calc
    _ ≤ scalarOrderWeight M j p^(2*j)*PowerSeries.coeff j (auxiliarySolutionUnit U 5):=he
    _ ≤ scalarOrderWeight M j p^(2*j)*((C₁+1)*B^j):=
      mul_le_mul_of_nonneg_left (hUnits 5 j) (by unfold scalarOrderWeight;positivity)
    _ = _:=by ring
end WP.HigherOrder
