import WPFormalization.Volumes.CanonicalUniformError
import WPFormalization.Volumes.CanonicalCoefficientExtension
import WPFormalization.Analysis.GevreyTwoOptimalTruncation
/-! The full ORIGINAL Theorem 10.2 is proved from the three genuine extraction sectors and the actual common holomorphic coefficient extension. One C/B/c/H is selected before every genus, frequency and truncation order. Closed-interval continuity, the prescribed one-sided critical value, all K<=c*sqrt(h) errors and the optimal floor truncation are retained. No source, comparison, matching, analytic-extension or remainder premise remains beyond P and p>=1. The public frozen statement is kept separately. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
theorem canonical_expansion_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c h₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < h₀ ∧
      GevreyExtension (extractedCoefficient P p) C B ∧
      (∀ j, ContinuousOn (extractedCoefficient P p j) (Set.Icc 0 y₀)) ∧
      (∀ j, extractedCoefficient P p j y₀ = criticalExtractedCoefficient P p j) ∧
      (∀ (g k K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) →
        let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
          ∑ j ∈ Finset.range (K+1), extractedCoefficient P p j Y/
            (complexity g p : ℝ)^j| ≤
          C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∃ c' a C' h₁ : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧ 0 < h₁ ∧
        ∀ (g k : ℕ), h₁ ≤ (complexity g p : ℝ) →
          let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
          |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (complexity g p)⌋₊+1),
              extractedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
                C'*Real.exp (-a*Real.sqrt (complexity g p))) := by
  obtain ⟨Ce,Be,c,H,hCe,hBe,hc,hH,herror⟩ := Analysis.canonical_uniform_coefficient_error P p hp
  obtain ⟨Ca,Ba,hCa,hBa,hfamily⟩ := Analysis.canonical_coefficient_gevrey_extension P p hp
  let C : ℝ := Ce+Ca
  let B : ℝ := Be+Ba
  have hC : 0 < C := add_pos hCe hCa
  have hB : 0 < B := add_pos hBe hBa
  have hCeC : Ce ≤ C := by dsimp [C]; linarith
  have hCaC : Ca ≤ C := by dsimp [C]; linarith
  have hBeB : Be ≤ B := by dsimp [B]; linarith
  have hBaB : Ba ≤ B := by dsimp [B]; linarith
  have hfamily' : GevreyExtension (extractedCoefficient P p) C B := by
    obtain ⟨Ω,F,hΩ,hcover,hFa,hFr,hFb⟩ := hfamily
    refine ⟨Ω,F,hΩ,hcover,hFa,hFr,?_⟩
    intro j z hz
    exact (hFb j z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hCaC (pow_le_pow_left₀ hBa.le hBaB j) (pow_nonneg hBa.le _) hC.le) (sq_nonneg _))
  have herror' : ∀ (g k K : ℕ), H ≤ (complexity g p : ℝ) →
      (K : ℝ) ≤ c*Real.sqrt (complexity g p) →
      let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
      |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
        ∑ j ∈ Finset.range (K+1), extractedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
          C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1) := by
    intro g k K hg hK
    exact (herror g k K hg hK).trans
      (gevreyTwo_majorant_mono Ce Be C B (complexity g p : ℝ) (K+1) hBe.le hC.le hCeC hBeB (hH.trans_le hg))
  refine ⟨C,B,c,H,hC,hB,hc,hH,hfamily',
    Analysis.continuousOn_of_gevreyExtension (extractedCoefficient P p) C B hfamily',?_,herror',?_⟩
  · intro j
    simp [extractedCoefficient,y₀_pos.ne']
  · obtain ⟨c',a,Hopt,hc',hc'c,ha,hHopt,hopt⟩ := Analysis.gevreyTwo_optimal_scalar B c hB hc
    refine ⟨c',a,C,max H Hopt,hc',hc'c,ha,hC,hH.trans_le (le_max_left _ _),?_⟩
    intro g k hg
    let h : ℝ := complexity g p
    let K := ⌊c'*Real.sqrt h⌋₊
    have hgH : H ≤ h := (le_max_left _ _).trans hg
    have hgOpt : Hopt ≤ h := (le_max_right _ _).trans hg
    have hK : (K : ℝ) ≤ c*Real.sqrt h :=
      (Nat.floor_le (mul_nonneg hc'.le (Real.sqrt_nonneg h))).trans
        (mul_le_mul_of_nonneg_right hc'c (Real.sqrt_nonneg h))
    have he := herror' g k K hgH hK
    have ht := hopt h hgOpt
    change B^(K+1)*((K+1).factorial : ℝ)^2/h^(K+1) ≤ Real.exp (-a*Real.sqrt h) at ht
    exact he.trans (by convert mul_le_mul_of_nonneg_left ht hC.le using 1 <;> ring)
end WP.HigherOrder
