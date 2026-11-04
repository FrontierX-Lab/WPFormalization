import WPFormalization.HigherOrder.MarkedExtensionProof
import WPFormalization.HigherOrder.MarkedRelativeGevrey
import WPFormalization.Analysis.GevreyTwoOptimalTruncation
/-! Original Theorem 8.2, with the prescribed canonical coefficients and all
common-neighborhood, real/logarithmic and optimal-truncation clauses.
The actual all-order log transport, endpoint matching and finite exponentiation
are supplied before the common constants are chosen. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma gevreyTwo_majorant_mono (C₀ B₀ C B h:ℝ) (N:ℕ)
    (hB₀:0 ≤ B₀) (hC:0 ≤ C) (hCC:C₀ ≤ C) (hBB:B₀ ≤ B) (hh:0<h):
    C₀*B₀^N*(N.factorial:ℝ)^2/h^N ≤ C*B^N*(N.factorial:ℝ)^2/h^N:=by
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul hCC (pow_le_pow_left₀ hB₀ hBB N) (pow_nonneg hB₀ N) hC)
    (sq_nonneg (N.factorial:ℝ))) (pow_nonneg hh.le N)

lemma full_expansion_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c h₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < h₀ ∧
      GevreyExtensionPair (logarithmicMarkedCoefficient P p) (markedCoefficient P p) C B ∧
      (∀ (g K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) → ∀ Y ∈ Set.Ico 0 y₀,
        |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
          ∑ j ∈ Finset.range (K+1), markedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
            C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∀ (g K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) → ∀ Y ∈ Set.Ico 0 y₀,
        |Real.log (Real.pi*markedF P g p (XR Y)/markedModel g p Y) -
          ∑ j ∈ Finset.range (K+1), logarithmicMarkedCoefficient P p j Y/
            (complexity g p : ℝ)^j| ≤
            C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∃ c' a C' h₁ : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧ 0 < h₁ ∧
        ∀ g : ℕ, h₁ ≤ (complexity g p : ℝ) → ∀ Y ∈ Set.Ico 0 y₀,
          |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (complexity g p)⌋₊+1),
              markedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
                C'*Real.exp (-a*Real.sqrt (complexity g p))) := by
  obtain ⟨Cp,Bp,hCp,hBp,hpair⟩:=markedCoefficient_common_complex_gevrey_two P p hp
  obtain ⟨Cr,Br,cr,Hr,hCr,hBr,hcr,hHr,hrel⟩:=actual_marked_relative_uniform_gevrey_two P p hp
  obtain ⟨Cl,Bl,cl,Hl,hCl,hBl,hcl,hHl,hlog⟩:=actual_marked_log_uniform_gevrey_two P p hp
  let C:=Cp+Cr+Cl
  let B:=Bp+Br+Bl
  let c:=min cr cl
  let H:=max Hr Hl
  have hC:0<C:=by dsimp[C];positivity
  have hB:0<B:=by dsimp[B];positivity
  have hc:0<c:=lt_min hcr hcl
  have hH:0<H:=hHr.trans_le (le_max_left _ _)
  have hpC:Cp ≤ C:=by dsimp[C];linarith
  have hrC:Cr ≤ C:=by dsimp[C];linarith
  have hlC:Cl ≤ C:=by dsimp[C];linarith
  have hpB:Bp ≤ B:=by dsimp[B];linarith
  have hrB:Br ≤ B:=by dsimp[B];linarith
  have hlB:Bl ≤ B:=by dsimp[B];linarith
  have hpair':GevreyExtensionPair (logarithmicMarkedCoefficient P p) (markedCoefficient P p) C B:=by
    obtain ⟨Ω,aC,LC,hΩ,hcover,ha,hrest,hbound⟩:=hpair
    refine ⟨Ω,aC,LC,hΩ,hcover,ha,hrest,?_⟩
    intro j z hz
    have hm:=gevreyTwo_majorant_mono Cp Bp C B 1 j hBp.le hC.le hpC hpB zero_lt_one
    simp only[one_pow,div_one] at hm
    exact (hbound j z hz).trans hm
  have hrelAll:∀g K:ℕ,H ≤ (complexity g p:ℝ)→
      (K:ℝ) ≤ c*Real.sqrt (complexity g p:ℝ)→∀Y∈Ico (0:ℝ) y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-
        ∑j∈Finset.range (K+1),markedCoefficient P p j Y/(complexity g p:ℝ)^j| ≤
        C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
    intro g K hg hK Y hY
    have hh:(0:ℝ)<complexity g p:=hH.trans_le hg
    have hr:=hrel g K ((le_max_left _ _).trans hg)
      (hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))) Y hY
    exact hr.trans (gevreyTwo_majorant_mono Cr Br C B _ (K+1) hBr.le hC.le hrC hrB hh)
  refine ⟨C,B,c,H,hC,hB,hc,hH,hpair',hrelAll,?_,?_⟩
  · intro g K hg hK Y hY
    have hh:(0:ℝ)<complexity g p:=hH.trans_le hg
    have hl:=hlog g K ((le_max_right _ _).trans hg)
      (hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))) Y hY
    have he:=hl.trans (gevreyTwo_majorant_mono Cl Bl C B _ (K+1) hBl.le hC.le hlC hlB hh)
    simpa only[prefactorLogError] using he
  · obtain ⟨c',a,Hopt,hc',hc'c,ha,hHopt,hopt⟩:=Analysis.gevreyTwo_optimal_scalar B c hB hc
    refine ⟨c',a,C,max H Hopt,hc',hc'c,ha,hC,hH.trans_le (le_max_left _ _),?_⟩
    intro g hg Y hY
    let h:ℝ:=complexity g p
    let K:=⌊c'*Real.sqrt h⌋₊
    have hgH:H ≤ h:=(le_max_left _ _).trans hg
    have hgOpt:Hopt ≤ h:=(le_max_right _ _).trans hg
    have hK:(K:ℝ) ≤ c*Real.sqrt h:=
      (Nat.floor_le (mul_nonneg hc'.le (Real.sqrt_nonneg h))).trans
        (mul_le_mul_of_nonneg_right hc'c (Real.sqrt_nonneg h))
    have he:=hrelAll g K hgH hK Y hY
    have ht:=hopt h hgOpt
    change B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) ≤ Real.exp (-a*Real.sqrt h) at ht
    apply he.trans
    convert mul_le_mul_of_nonneg_left ht hC.le using 1 <;>ring
end WP.HigherOrder
