import WPFormalization.Statements.UniformRecursiveExpansionsTarget
import WPFormalization.HigherOrder.CanonicalCoherenceProof
/-! Common-constant assembly of the full original C.3 specification.
The two finite-data goals remain explicit inputs here; this helper is not the
final paper theorem and has no Blueprint attribute. All analytic, coherence
and actual-remainder inputs are supplied by their proved canonical producers. -/
noncomputable section
namespace WP.HigherOrder
open Set

lemma recursive_geometric_weight_mono (C₀ C B₀ B W₀ W : ℝ) (n : ℕ)
    (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀) (hW₀ : 0 ≤ W₀)
    (hC : C₀ ≤ C) (hB : B₀ ≤ B) (hW : W₀ ≤ W) :
    C₀*B₀^n*W₀^(2*n) ≤ C*B^n*W^(2*n) := by
  have hCnon : 0 ≤ C := hC₀.trans hC
  have hBnon : 0 ≤ B := hB₀.trans hB
  have hWnon : 0 ≤ W := hW₀.trans hW
  gcongr

lemma recursive_profile_weight_mono (M₀ M : ℕ) (hM : M₀ ≤ M) (n : ℕ) (d : List ℕ) :
    profileOrderWeight (M₀:ℝ) n d ≤ profileOrderWeight (M:ℝ) n d := by
  have hm : (M₀:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  unfold profileOrderWeight
  gcongr

lemma recursive_scalar_weight_mono (M₀ M : ℕ) (hM : M₀ ≤ M) (n p : ℕ) :
    scalarOrderWeight (M₀:ℝ) n p ≤ scalarOrderWeight (M:ℝ) n p := by
  have hm : (M₀:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  unfold scalarOrderWeight
  gcongr

lemma full_recursive_expansion_assembly (P : PsiTheory)
    (hfinite : KernelFiniteData.PolynomialDependenceTarget P)
    (hstrata : KernelFiniteData.ProfileBoundaryPolynomialTarget P) :
    UniformRecursiveExpansionsTarget P := by
  obtain ⟨Ω,R,C₀,B₀,M₀,hΩ,hΩv,hcover,hC₀,hB₀,hM₀,hR,hunit,hraw,hR0,hR',hkernel,
    hprofA,hscalA,hprofR,hscalR,hprofB,hscalB⟩ :=
      ComplexCanonical.canonicalCoefficientBoundsTarget_proof P
  obtain ⟨C₁,B₁,M₁,hC₁,hB₁,hM₁,hprofile,hscalar⟩ := canonical_uniform_recursive_remainders P
  let C : ℝ := max C₀ C₁
  let B : ℝ := max B₀ B₁
  let M : ℕ := max M₀ M₁
  have hCM0 : C₀ ≤ C := le_max_left _ _
  have hCM1 : C₁ ≤ C := le_max_right _ _
  have hBM0 : B₀ ≤ B := le_max_left _ _
  have hBM1 : B₁ ≤ B := le_max_right _ _
  have hMM0 : M₀ ≤ M := le_max_left _ _
  have hMM1 : M₁ ≤ M := le_max_right _ _
  refine ⟨Ω,R,C,B,M,hΩ,hΩv,hcover,hC₀.trans_le hCM0,hB₀.trans_le hBM0,
    hM₀.trans hMM0,hR,hunit,hraw,hR0,hR',hkernel,hprofA,hscalA,hprofR,hscalR,?_,?_,?_,?_,?_,hfinite,hstrata⟩
  · intro n d hd z hz
    exact (hprofB n d hd z hz).trans
      (recursive_geometric_weight_mono C₀ C B₀ B _ _ n hC₀.le hB₀.le
        (by unfold profileOrderWeight;positivity) hCM0 hBM0 (recursive_profile_weight_mono M₀ M hMM0 n d))
  · intro n p hp z hz
    exact (hscalB n p hp z hz).trans
      (recursive_geometric_weight_mono C₀ C B₀ B _ _ n hC₀.le hB₀.le
        (by unfold scalarOrderWeight;positivity) hCM0 hBM0 (recursive_scalar_weight_mono M₀ M hMM0 n p))
  · intro g d hd hstable hh L hL Y hY
    exact (hprofile g d hd hstable hh L hL Y hY).trans
      (div_le_div_of_nonneg_right
        (recursive_geometric_weight_mono C₁ C B₁ B _ _ L hC₁.le hB₁.le
          (by unfold profileOrderWeight;positivity) hCM1 hBM1 (recursive_profile_weight_mono M₁ M hMM1 L d))
        (by positivity))
  · intro g p hp hstable hh L hL Y hY
    exact (hscalar g p hp hstable hh L hL Y hY).trans
      (div_le_div_of_nonneg_right
        (recursive_geometric_weight_mono C₁ C B₁ B _ _ L hC₁.le hB₁.le
          (by unfold scalarOrderWeight;positivity) hCM1 hBM1 (recursive_scalar_weight_mono M₁ M hMM1 L p))
        (by positivity))
  · intro K hK d hd i hi z hz
    exact ComplexCanonical.canonical_adjacent_on_complex_domain_of_recursiveRemainder P
      (canonical_uniform_recursive_remainders P) Ω hΩv hcover R hprofA hprofR K hK d hd i hi z hz
end WP.HigherOrder
