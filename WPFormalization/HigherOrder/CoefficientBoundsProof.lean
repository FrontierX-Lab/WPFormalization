import WPFormalization.HigherOrder.CanonicalNormInduction
import WPFormalization.HigherOrder.CoefficientBoundsAssembly
/-! Original Lemma C.4, proved against the separately frozen specification. The common actual complex inputs, seven-component polynomial analytic solution, complete canonical norm induction, Nat choices of b/M, uniform exponential coefficient bound, physical restriction and holomorphy are all instantiated. The public producer has only the original numerical PsiTheory parameter and no additional majorant or coefficient-bound premise. -/
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma canonicalCoefficientBoundsTarget_proof (P:PsiTheory) : CanonicalCoefficientBoundsTarget P := by
  obtain ⟨Ω,R,ρ,C₀,A₀,hΩ,hΩv,hcover,hρ,hC₀,hA₀,hR,hunit,hraw,hR0,hR',hA,hAb,hcoef,hbound,hcrit,hmom,hsmallA,hsmallB,hphysical⟩:=
    common_complex_canonical_inputs
  obtain ⟨T,hT,hsmall⟩:=hsmallB P
  obtain ⟨B₀,M₀,hB₀,hM₀,hInv⟩:=hierarchyJet_auxiliary_norm_invariant ρ C₀ A₀ hρ hC₀ hA₀
  let b:ℕ:=⌈B₀+2*T*A₀⌉₊
  have hb:B₀+2*T*A₀ ≤ (b:ℝ):=Nat.le_ceil _
  let M:ℕ:=max 2 ⌈M₀⌉₊
  have hMtwo:2 ≤ M:=le_max_left _ _
  have hMbig:M₀ ≤ (M:ℝ):=(Nat.le_ceil M₀).trans (by exact_mod_cast (le_max_right 2 ⌈M₀⌉₊))
  obtain ⟨U,h0,hfixed,hU,C₁,B₁,hC₁,hB₁,hgeometric⟩:=auxiliaryMajorantSolution_exists b
  let B:=max B₁ 1
  have hB:0<B:=lt_of_lt_of_le hB₁ (le_max_left _ _)
  have hB1:1 ≤ B:=le_max_right _ _
  have hUnits (i:Fin 7) (j:ℕ) :
      PowerSeries.coeff j (auxiliarySolutionUnit U i) ≤ (C₁+1)*B^j:=by
    rw[auxiliarySolutionUnit,map_add]
    have hOne:PowerSeries.coeff j (1:WP.HigherOrder.Series) ≤ 1:=by
      rw[PowerSeries.coeff_one];split_ifs<;>norm_num
    have hPow:B₁^j ≤ B^j:=pow_le_pow_left₀ hB₁.le (le_max_left _ _) j
    have hOnePow:1 ≤ B^j:=one_le_pow₀ hB1
    calc
      _ ≤ 1+C₁*B^j:=add_le_add hOne ((hgeometric i j).trans (mul_le_mul_of_nonneg_left hPow hC₁.le))
      _ ≤ _:=by nlinarith
  have hTables (z:ℂ) (hz:z∈Ω) (N:ℕ) :
      JetMajorantInvariant (M:ℝ) N (hierarchyJet P R z N) U:=by
    apply hInv P R z (fun l=>(hbound z hz l).2.1) (fun l=>(hbound z hz l).2.2)
      (hAb z hz).2.1 (hAb z hz).2.2 T hT (fun g d hs=>?_) b hb U h0 hfixed hU (M:ℝ) hMbig N
    exact hsmall g d hs z hz
  have hProfile:∀j:ℕ,∀d:List ℕ,1 ≤ d.length→∀z∈Ω,
      ‖profileCoefficient P R z d j‖ ≤ (C₁+1)*B^j*(profileOrderWeight (M:ℝ) j d)^(2*j):=by
    intro j d hd z hz
    have hh:=(hTables z hz j).1 j le_rfl d hd
    change ‖profileCoefficient P R z d j‖ ≤ (profileOrderWeight (M:ℝ) j d)^(2*j)*
      PowerSeries.coeff j (auxiliarySolutionUnit U 2) at hh
    calc
      _ ≤ (profileOrderWeight (M:ℝ) j d)^(2*j)*PowerSeries.coeff j (auxiliarySolutionUnit U 2):=hh
      _ ≤ (profileOrderWeight (M:ℝ) j d)^(2*j)*((C₁+1)*B^j):=
        mul_le_mul_of_nonneg_left (hUnits 2 j) (by unfold profileOrderWeight;positivity)
      _=_:=by ring
  have hCusp:∀j p:ℕ,1 ≤ p→∀z∈Ω,
      ‖cuspCoefficient P R z p j‖ ≤ (C₁+1)*B^j*(scalarOrderWeight (M:ℝ) j p)^(2*j):=by
    intro j p hp z hz
    have hh:=(hTables z hz j).2.1 j le_rfl p hp
    change ‖cuspCoefficient P R z p j‖ ≤ (scalarOrderWeight (M:ℝ) j p)^(2*j)*
      PowerSeries.coeff j (auxiliarySolutionUnit U 3) at hh
    calc
      _ ≤ (scalarOrderWeight (M:ℝ) j p)^(2*j)*PowerSeries.coeff j (auxiliarySolutionUnit U 3):=hh
      _ ≤ (scalarOrderWeight (M:ℝ) j p)^(2*j)*((C₁+1)*B^j):=
        mul_le_mul_of_nonneg_left (hUnits 3 j) (by unfold scalarOrderWeight;positivity)
      _=_:=by ring
  have hGenus:∀j p:ℕ,1 ≤ p→∀z∈Ω,
      ‖genusCoefficient P R z p j‖ ≤ (C₁+1)*B^j*(scalarOrderWeight (M:ℝ) j p)^(2*j):=by
    intro j p hp z hz
    by_cases hp1:p=1
    · subst p
      have hh:=(hTables z hz j).2.2.2 j le_rfl
      change ‖genusCoefficient P R z 1 j‖ ≤ (scalarOrderWeight (M:ℝ) j 1)^(2*j)*
        PowerSeries.coeff j (auxiliarySolutionUnit U 6) at hh
      calc
        _ ≤ (scalarOrderWeight (M:ℝ) j 1)^(2*j)*PowerSeries.coeff j (auxiliarySolutionUnit U 6):=hh
        _ ≤ (scalarOrderWeight (M:ℝ) j 1)^(2*j)*((C₁+1)*B^j):=
          mul_le_mul_of_nonneg_left (hUnits 6 j) (by unfold scalarOrderWeight;positivity)
        _=_:=by ring
    · have hp2:2 ≤ p:=by omega
      have hh:=(hTables z hz j).2.2.1 j le_rfl p hp2
      change ‖genusCoefficient P R z p j‖ ≤ (scalarOrderWeight (M:ℝ) j p)^(2*j)*
        PowerSeries.coeff j (auxiliarySolutionUnit U 4) at hh
      calc
        _ ≤ (scalarOrderWeight (M:ℝ) j p)^(2*j)*PowerSeries.coeff j (auxiliarySolutionUnit U 4):=hh
        _ ≤ (scalarOrderWeight (M:ℝ) j p)^(2*j)*((C₁+1)*B^j):=
          mul_le_mul_of_nonneg_left (hUnits 4 j) (by unfold scalarOrderWeight;positivity)
        _=_:=by ring
  exact coefficientBoundsTarget_of_uniform_norm_bounds Ω hΩ hΩv hcover P R hR
    (fun z hz=>(hunit z hz).1) hraw hR0 hR' ρ C₀ hρ hC₀.le
    (fun l=>(hcoef l).2.1) (fun l z hz=>(hbound z hz l).2.1)
    (fun l=>(hcoef l).2.2.1) (fun l z hz=>(hbound z hz l).2.2)
    hA (fun z hz=>(hAb z hz).1) (fun g d=>(hsmallA P g d).1) T hT hsmall
    (C₁+1) B M (by positivity) hB hMtwo hProfile hCusp hGenus
end WP.HigherOrder.ComplexCanonical
