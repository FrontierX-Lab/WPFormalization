import WPFormalization.HigherOrder.PainleveMellin
import WPFormalization.HigherOrder.PainleveJumpGevrey
import WPFormalization.Analysis.GammaContourTransfer
import WPFormalization.HigherOrder.EndpointFallingReexpansion
/-! The actual zero-instanton coefficients match the canonical endpointZ
series with an order-uniform Gevrey-1 remainder in a linear genus window.
The proof transports the genuine PI jump through the coefficient contour,
keeps low integrals and the inner-circle error, and re-expands the exact
falling-Gamma products. Only the mature GIKM/CCH existence data are deferred.
No uniform PI asymptotic is imported as an external assertion. -/
noncomputable section
namespace WP.HigherOrder
open Set MeasureTheory
lemma normalizedPainleveJump_real_remainder (G:External.PainleveAnalytic.GIKMData)
    (L:ℕ) (ξ:ℝ) :
    |realNormalizedPainleveJump G ξ-∑j∈Finset.range L,(jumpCoefficient j:ℝ)/ξ^j|≤
      ‖normalizedPainleveJump G ξ-∑j∈Finset.range L,((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j‖ := by
  have hc : (((∑j∈Finset.range L,(jumpCoefficient j:ℝ)/ξ^j):ℝ):ℂ)=
      (∑j∈Finset.range L,((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j) := by push_cast;rfl
  rw [←hc]
  simpa only [realNormalizedPainleveJump,Complex.sub_re,Complex.ofReal_re] using
    Complex.abs_re_le_norm (normalizedPainleveJump G ξ-
      (((∑j∈Finset.range L,(jumpCoefficient j:ℝ)/ξ^j):ℝ):ℂ))
lemma normalizedZeroInstanton_falling_gevrey_of_jump (G:External.PainleveAnalytic.GIKMData)
    (hjump:∃C B R:ℝ,0<C ∧ 0<B ∧ 0<R ∧ ∀L:ℕ,∀ξ:ℝ,R≤ξ →
      ‖normalizedPainleveJump G ξ-
        ∑j∈Finset.range L,((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j‖≤
        C*B^L*(L.factorial:ℝ)/ξ^L) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀g:ℕ,3≤g → ∀L:ℕ,1≤L → 2*L≤g →
      |External.normalizedZeroInstanton g-
        (∑j∈Finset.range L,(jumpCoefficient j:ℝ)*Real.Gamma (2*(g:ℝ)-1/2-(j:ℝ)))/
          Real.Gamma (2*(g:ℝ)-1/2)|≤C*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
  obtain ⟨C,B,R,hC,hB,hR,hjump⟩:=hjump
  obtain ⟨ρ,hρ,hRρ⟩:=painleve_contour_radius_above G R
  obtain ⟨C₀,D,hC₀,hD,hcircle⟩:=painleve_real_mellin_contour G ρ hρ
  have hρp : 0<ρ:=G.contour_radius_pos.trans_le hρ
  have ha : 0≤External.painleveAction*ρ^(5/2:ℝ):=
    (mul_pos painleveAction_pos (Real.rpow_pos_of_pos hρp _)).le
  apply WP.Analysis.gamma_contour_gevrey_transfer External.normalizedZeroInstanton
    (realNormalizedPainleveJump G) (fun j:ℕ=>(jumpCoefficient j:ℝ))
    (External.painleveAction*ρ^(5/2:ℝ)) C₀ D C B 1 32 1 ha hC₀.le hD.le hC.le hB.le
    (by norm_num) (by norm_num) (painleve_real_jump_aestronglyMeasurable G ρ hρ)
    (fun j=>by simpa only [one_mul] using jumpCoefficient_real_factorial_bound j)
    (fun L hL ξ hξ=>(normalizedPainleveJump_real_remainder G L ξ).trans
      (hjump L ξ (hRρ.trans hξ.le)))
    (fun g hg=>(hcircle g hg).2)

lemma normalizedZeroInstanton_endpointZ_gevrey_of_jump (G:External.PainleveAnalytic.GIKMData)
    (hjump:∃C B R:ℝ,0<C ∧ 0<B ∧ 0<R ∧ ∀L:ℕ,∀ξ:ℝ,R≤ξ →
      ‖normalizedPainleveJump G ξ-
        ∑j∈Finset.range L,((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j‖≤
        C*B^L*(L.factorial:ℝ)/ξ^L) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀g:ℕ,3≤g → ∀L:ℕ,1≤L →
      4*(L:ℝ)≤((2*g-2:ℕ):ℝ) →
      |External.normalizedZeroInstanton g-
        ∑j∈Finset.range L,PowerSeries.coeff j endpointZ*((2*g-2:ℕ):ℝ)⁻¹^j|≤
      C*B^L*(L.factorial:ℝ)*((2*g-2:ℕ):ℝ)⁻¹^L := by
  obtain ⟨C,B,hC,hB,he⟩:=normalizedZeroInstanton_falling_gevrey_of_jump G hjump
  let Q:ℝ:=2*B+128*Real.exp 1
  have hQ:0<Q:=by dsimp[Q];positivity
  have hBq:2*B≤Q:=by dsimp[Q];linarith [Real.exp_pos 1]
  have hEq:128*Real.exp 1≤Q:=by dsimp[Q];linarith
  refine ⟨C+2,Q,by positivity,hQ,?_⟩
  intro g hg L hL hLg
  let h:ℝ:=((2*g-2:ℕ):ℝ)
  have hhR : h=2*(g:ℝ)-2 := by
    dsimp [h]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hgr : (3:ℝ)≤g:=by exact_mod_cast hg
  have hgpos : (0:ℝ)<g:=by linarith
  have hh : 0<h:=by rw[hhR];linarith
  have h2L : 2*L≤g := by
    have hh' : 2*(L:ℝ)≤g:=by change 4*(L:ℝ)≤h at hLg;linarith
    exact_mod_cast hh'
  have hν : 2*(g:ℝ)-1/2=h+3/2:=by rw[hhR];ring
  have hfirst:=he g hg L hL h2L
  rw[hν,Finset.sum_div] at hfirst
  have hsum : (∑j∈Finset.range L,(jumpCoefficient j:ℝ)*Real.Gamma (h+3/2-(j:ℝ))/Real.Gamma (h+3/2))=
      ∑j∈Finset.range L,(jumpCoefficient j:ℝ)*(Real.Gamma (h+3/2-(j:ℝ))/Real.Gamma (h+3/2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw[hsum] at hfirst
  have hsecond:=gamma_endpoint_falling_sum_reexpansion h L hL hLg
  have hinv : (g:ℝ)⁻¹≤2*h⁻¹ := by
    have hediv : 1/(g:ℝ)≤2/h := by
      apply (div_le_div_iff₀ hgpos hh).mpr
      rw[hhR]
      linarith
    simpa only [one_div,div_eq_mul_inv,one_mul] using hediv
  have hfirstBound : C*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L≤
      C*Q^L*(L.factorial:ℝ)*h⁻¹^L := by
    calc
      _≤C*B^L*(L.factorial:ℝ)*(2*h⁻¹)^L := by gcongr
      _=C*(2*B)^L*(L.factorial:ℝ)*h⁻¹^L:=by rw[mul_pow,mul_pow];ring
      _≤_:=by gcongr
  have hsecondBound : 2*(128*Real.exp 1)^L*(L.factorial:ℝ)*h⁻¹^L≤
      2*Q^L*(L.factorial:ℝ)*h⁻¹^L := by gcongr
  change |External.normalizedZeroInstanton g-∑j∈Finset.range L,
    PowerSeries.coeff j endpointZ*h⁻¹^j|≤_
  calc
    _≤|External.normalizedZeroInstanton g-
        ∑j∈Finset.range L,(jumpCoefficient j:ℝ)*(Real.Gamma (h+3/2-(j:ℝ))/Real.Gamma (h+3/2))|+
        |(∑j∈Finset.range L,(jumpCoefficient j:ℝ)*(Real.Gamma (h+3/2-(j:ℝ))/Real.Gamma (h+3/2)))-
          ∑j∈Finset.range L,PowerSeries.coeff j endpointZ*h⁻¹^j|:=abs_sub_le _ _ _
    _≤C*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L+2*(128*Real.exp 1)^L*(L.factorial:ℝ)*h⁻¹^L:=add_le_add hfirst hsecond
    _≤C*Q^L*(L.factorial:ℝ)*h⁻¹^L+2*Q^L*(L.factorial:ℝ)*h⁻¹^L:=add_le_add hfirstBound hsecondBound
    _=_:=by ring

/-- The actual zero-instanton coefficients have the canonical endpointZ
Gevrey expansion, conditional only on the licensed mature PI data. -/
theorem normalizedZeroInstanton_endpointZ_gevrey :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀g:ℕ,3≤g → ∀L:ℕ,1≤L →
      4*(L:ℝ)≤((2*g-2:ℕ):ℝ) →
      |External.normalizedZeroInstanton g-
        ∑j∈Finset.range L,PowerSeries.coeff j endpointZ*((2*g-2:ℕ):ℝ)⁻¹^j|≤
      C*B^L*(L.factorial:ℝ)*((2*g-2:ℕ):ℝ)⁻¹^L := by
  obtain ⟨G⟩:=External.PainleveAnalytic.exists_gikm_data
  obtain ⟨D⟩:=External.PainleveAnalytic.exists_cch_data
  exact normalizedZeroInstanton_endpointZ_gevrey_of_jump G (normalizedPainleveJump_gevrey G D)

/-- A linear genus window, with constants independent of the truncation order. -/
theorem normalizedZeroInstanton_endpointZ_expansion :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀g:ℕ,4≤g → ∀K:ℕ,(K:ℝ)≤(g:ℝ)/8 →
      |External.normalizedZeroInstanton g-
        ∑j∈Finset.range (K+1),PowerSeries.coeff j endpointZ*((2*g-2:ℕ):ℝ)⁻¹^j|≤
      C*B^(K+1)*((K+1).factorial:ℝ)*((2*g-2:ℕ):ℝ)⁻¹^(K+1) := by
  obtain ⟨C,B,hC,hB,he⟩:=normalizedZeroInstanton_endpointZ_gevrey
  refine ⟨C,B,hC,hB,?_⟩
  intro g hg K hK
  apply he g (by omega) (K+1) (by omega)
  have hgr : (4:ℝ)≤g:=by exact_mod_cast hg
  rw [Nat.cast_sub (by omega : 2≤2*g)]
  push_cast
  linarith

end WP.HigherOrder
