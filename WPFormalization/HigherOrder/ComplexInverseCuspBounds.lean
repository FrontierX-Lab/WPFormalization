import WPFormalization.HigherOrder.InverseCuspBounds
import WPFormalization.HigherOrder.TransportCoefficientComplex
/-! Actual inverse cusp coefficients have uniform bounds and holomorphy on one common complex domain. The proved seven-component canonical norm invariant supplies the inverse component; no new coefficient estimate or analytic existence is assumed. -/
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open Set PowerSeries
lemma common_complex_inverse_cusp_bounds (P:PsiTheory) :
    ∃(Ω:Set ℂ)(R:ℂ→ℂ)(C B:ℝ)(M:ℕ),
      IsOpen Ω ∧ Convex ℝ Ω ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧0<C ∧0<B ∧2 ≤ M ∧
      AnalyticOnNhd ℂ R Ω ∧(∀z∈Ω,WP.Analysis.complexAUnit z≠0) ∧
      (∀Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧R y₀=0 ∧deriv R y₀=-3 ∧
      AnalyticOnNhd ℂ (kernelA R) Ω ∧(∀z∈Ω,kernelA R z≠0) ∧
      (∀n p:ℕ,1 ≤ p→AnalyticOnNhd ℂ (fun z=>cuspCoefficient P R z p n) Ω) ∧
      (∀n p:ℕ,1 ≤ p→∀z∈Ω,‖PowerSeries.coeff n ((formalCusp P R z p)⁻¹)‖ ≤
        C*B^n*WP.HigherOrder.scalarOrderWeight (M:ℝ) n p^(2*n)) := by
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

  have hInverse:∀j p:ℕ,1 ≤ p→∀z∈Ω,
      ‖PowerSeries.coeff j ((formalCusp P R z p)⁻¹)‖ ≤
        (C₁+1)*B^j*WP.HigherOrder.scalarOrderWeight (M:ℝ) j p^(2*j):=by
    intro j p hp z hz
    have hc:∀i ≤ j,‖PowerSeries.coeff i (formalCusp P R z p)‖ ≤
        WP.HigherOrder.scalarOrderWeight (M:ℝ) j p^(2*i)*PowerSeries.coeff i (auxiliarySolutionUnit U 3):=by
      intro i hi
      have hb:=(hTables z hz j).2.1 i hi p hp
      rw[hierarchy_cusp_stable P R z p j i hi] at hb
      have hw:WP.HigherOrder.scalarOrderWeight (M:ℝ) i p ≤ WP.HigherOrder.scalarOrderWeight (M:ℝ) j p:=by
        unfold WP.HigherOrder.scalarOrderWeight
        have hm:=mul_le_mul_of_nonneg_left (show (i:ℝ) ≤ j by exact_mod_cast hi) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
        linarith
      simp only[formalCusp,PowerSeries.coeff_mk]
      apply hb.trans
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by unfold WP.HigherOrder.scalarOrderWeight;positivity) hw _)
        (auxiliarySolutionUnit_nonnegative U hU 3 i)
    have he:=scaled_coeff_unit_inverse_bound (formalCusp P R z p) (auxiliarySolutionUnit U 3)
      (WP.HigherOrder.scalarOrderWeight (M:ℝ) j p) (by unfold WP.HigherOrder.scalarOrderWeight;positivity)
      (formalCusp_constant P R z p) (by simpa only[PowerSeries.coeff_zero_eq_constantCoeff] using auxiliarySolutionUnit_coeff_zero U h0 3)
      (auxiliarySolutionUnit_nonnegative U hU 3) j hc
    have hW:inverseUnitMajorant (auxiliarySolutionUnit U 3)=auxiliarySolutionUnit U 5:=
      (auxiliaryMajorant_resolvents b U h0 hfixed).2.1.symm
    rw[hW] at he
    apply he.trans
    have hb:=mul_le_mul_of_nonneg_left (hUnits 5 j)
      (by unfold WP.HigherOrder.scalarOrderWeight;positivity:0 ≤ WP.HigherOrder.scalarOrderWeight (M:ℝ) j p^(2*j))
    convert hb using 1 <;>ring
  have hhol:=canonical_holomorphy_of_exponential_profile_bound Ω hΩ P R ρ C₀ hρ hC₀.le
    (fun l=>(hcoef l).2.1) (fun l z hz=>(hbound z hz l).2.1)
    (fun l=>(hcoef l).2.2.1) (fun l z hz=>(hbound z hz l).2.2)
    hA (fun z hz=>(hAb z hz).1) (fun g d=>(hsmallA P g d).1) T hT hsmall
    (M:ℝ) (by exact_mod_cast (show 1 ≤ M by omega)) (C₁+1) B (by positivity) hB.le hProfile
  exact ⟨Ω,R,C₁+1,B,M,hΩ,hΩv,hcover,by positivity,hB,hMtwo,hR,
    (fun z hz=>(hunit z hz).1),hraw,hR0,hR',hA,(fun z hz=>(hAb z hz).1),
    (fun n p hp=>(hhol n).2.1 p),hInverse⟩
end WP.HigherOrder.ComplexCanonical
