import WPFormalization.Statements.CoefficientBoundsTarget
import WPFormalization.HigherOrder.ComplexHierarchyAnalyticStep
/-! Assembly against the frozen Lemma C.4 specification. The uniform norm
bounds are explicit remaining premises of this glue theorem; this is not an
assertion that they already hold. Actual input existence, scalar extension
and the complete analytic induction are all proved in imported modules. -/
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace WP.HigherOrder.ComplexCanonical

lemma coefficientBoundsTarget_of_uniform_norm_bounds (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hconv : Convex ℝ Ω) (hcover : ∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (P : PsiTheory) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hunit : ∀z∈Ω,WP.Analysis.complexAUnit z≠0)
    (hraw : ∀Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hR0 : R y₀=0) (hR' : deriv R y₀=-3)
    (ρ C₀ : ℝ) (hρ : 1<ρ) (hC₀ : 0≤C₀)
    (hwa : ∀l,AnalyticOnNhd ℂ (WP.Analysis.complexWeightCoeff R l) Ω)
    (hwg : ∀l z,z∈Ω → ‖WP.Analysis.complexWeightCoeff R l z‖≤C₀/ρ^l)
    (hba : ∀l,AnalyticOnNhd ℂ (WP.Analysis.complexDilatonCoefficient R l) Ω)
    (hbg : ∀l z,z∈Ω → ‖WP.Analysis.complexDilatonCoefficient R l z‖≤C₀/ρ^l)
    (hA : AnalyticOnNhd ℂ (kernelA R) Ω) (hA0 : ∀z∈Ω,kernelA R z≠0)
    (hsa : ∀g d,AnalyticOnNhd ℂ (WP.Analysis.complexSmallW P R g d) Ω)
    (T : ℝ) (hT : 1≤T)
    (hsb : ∀g:ℕ,∀d:List ℕ,Stable g d.length → ∀z∈Ω,
      ‖WP.Analysis.complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (C B : ℝ) (M : ℕ) (hC : 0<C) (hB : 0<B) (hM : 2≤M)
    (hprofile : ∀j:ℕ,∀d:List ℕ,1≤d.length → ∀z∈Ω,
      ‖profileCoefficient P R z d j‖≤C*B^j*(profileOrderWeight (M:ℝ) j d)^(2*j))
    (hcusp : ∀j p:ℕ,1≤p → ∀z∈Ω,
      ‖cuspCoefficient P R z p j‖≤C*B^j*(scalarOrderWeight (M:ℝ) j p)^(2*j))
    (hgenus : ∀j p:ℕ,1≤p → ∀z∈Ω,
      ‖genusCoefficient P R z p j‖≤C*B^j*(scalarOrderWeight (M:ℝ) j p)^(2*j)) :
    CanonicalCoefficientBoundsTarget P := by
  have hM1 : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
  have hhol := canonical_holomorphy_of_exponential_profile_bound Ω hΩ P R ρ C₀ hρ hC₀ hwa hwg hba hbg
    hA hA0 hsa T hT hsb (M:ℝ) hM1 C B hC.le hB.le hprofile
  have hclosed := WP.Analysis.normalized_complex_kernels_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit
  refine ⟨Ω,R,2*C,B,M,hΩ,hconv,hcover,by positivity,hB,hM,hR,hunit,hraw,hR0,hR',hclosed,?_,?_,?_,?_,?_,?_⟩
  · intro j d hd
    exact (hhol j).1 d
  · intro j p hp
    exact ⟨(hhol j).2.1 p,(hhol j).2.2 p⟩
  · intro j d hd Y hY
    exact (canonical_coefficients_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit P Y hY j).1 d
  · intro j p hp Y hY
    have hh := canonical_coefficients_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit P Y hY j
    exact ⟨hh.2.1 p,hh.2.2 p⟩
  · intro j d hd z hz
    apply (hprofile j d hd z hz).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : C≤2*C)
      (pow_nonneg hB.le j)) (pow_nonneg (by unfold profileOrderWeight;positivity) _)
  · intro j p hp z hz
    apply (add_le_add (hcusp j p hp z hz) (hgenus j p hp z hz)).trans_eq
    ring

end WP.HigherOrder.ComplexCanonical
