import WPFormalization.Volumes.OriginFourierIdentities
import WPFormalization.Volumes.SaddleCoefficientNormalization
/-! Actual positive extractionQ and uniformly bounded finite-source Fourier
prefactors in the non-tiny frequency regime. Relative source error controls
the prefactor difference through an exact algebraic identity. -/
noncomputable section
namespace WP.Analysis
open Set
lemma extractionQ_pos_at_positive_saddle (g p k:ℕ)(hs:Stable g p)(x:ℝ)
    (hh:0<(complexity g p:ℝ))(hk:1≤k)(hx:x∈Ioo (0:ℝ) xCritical)
    (hroot:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x):0<extractionQ g p k:=by
  have hy:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hm:=markedModel_pos_parameter g p hs (inverseY x) hy
  have hv:0<WP.euler WP.Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hkp:0<(k:ℝ):=by exact_mod_cast (show 0<k by omega)
  have hpc:0<poissonCenter k:=by unfold poissonCenter;positivity
  have hxp:0<x:=hx.1
  rw[extractionQ_at_positive_saddle g p k x hh hk hx hroot]
  positivity
lemma normalizedFiniteModel_prefactor_bound_nonTiny (κlo:ℝ)(hκlo:0<κlo):
    ∃H:ℝ,0<H ∧ ∀(P:PsiTheory)(g p k J:ℕ),H≤(complexity g p:ℝ)→
      κlo*Real.sqrt (complexity g p:ℝ)≤(k:ℝ)→Stable g p→
      ∀(S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(x:ℝ),x∈Ioo (0:ℝ) xCritical→
      (k:ℝ)=(complexity g p:ℝ)*WP.Psi x→S (x:ℂ)=(extractionS x:ℂ)→Bc (x:ℂ)=(extractionB p x:ℂ)→
      ‖HigherOrder.finiteMarkedFactor L (complexity g p:ℝ) J (inverseY x:ℂ)‖≤2→
      let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
      let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
      ‖HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))‖≤4*Real.sqrt (2*Real.pi):=by
  obtain ⟨H,hH,hbound⟩:=marked_model_saddle_prefactor_bound_nonTiny κlo hκlo
  refine ⟨H,hH,?_⟩
  intro P g p k J hg hk hs S Bc L x hx hroot hS hBc hP
  dsimp only
  rw[normalizedFiniteMarkedModel_at_physical P g p J hs S Bc L x ⟨hx.1.le,hx.2⟩ hS hBc]
  exact hbound g p k hg hk hs x hx hroot _ hP
lemma normalizedFiniteModel_prefactor_difference (P:PsiTheory)(g p k J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(x D ε:ℝ)
    (hM:HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0)
    (hB:‖HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)/
      ((x:ℂ)^k*(Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):ℂ)*
        ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ))‖≤D)
    (hε:0≤ε)
    (hrel:‖HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)/
      HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖≤ε):
    ‖HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)/
      ((x:ℂ)^k*(Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):ℂ)*
        ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ))-
      HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)/
      ((x:ℂ)^k*(Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):ℂ)*
        ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ))‖≤D*ε:=by
  let F:ℂ:=HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)
  let M:ℂ:=HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)
  let A:ℂ:=(x:ℂ)^k*(Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):ℂ)*
    ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)
  have hid:F/A-M/A=(M/A)*(F/M-1):=by
    calc _=((F/M)*M-M)/A:=by rw[div_mul_cancel₀ F hM];ring
         _= _:=by ring
  change ‖F/A-M/A‖≤_
  rw[hid,norm_mul]
  exact mul_le_mul hB hrel (norm_nonneg _) ((norm_nonneg _).trans hB)
end WP.Analysis
