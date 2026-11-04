import WPFormalization.Analysis.PoissonCentralLower
import WPFormalization.Volumes.SaddleModelNormalization
/-! Actual Q-normalized Fourier prefactors and their single relative-error transfer. Exact identities hold at every positive saddle; uniform bounds apply to the non-tiny frequency window and preserve the given finite-model value. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma marked_model_saddle_prefactor_exact (g p k:ℕ)(hs:Stable g p)(x:ℝ)
    (hh:0<(complexity g p:ℝ))(hk:1≤k)(hx:x∈Ioo (0:ℝ) xCritical)
    (hsaddle:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x)(z:ℂ):
    let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
    let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
    (((markedModel g p (inverseY x)/markedModel g p 0:ℝ):ℂ)*z)/
      ((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))=z/((poissonCenter k*Real.sqrt (k:ℝ):ℝ):ℂ):=by
  dsimp only
  have hY:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hMY:markedModel g p (inverseY x)≠0:=(markedModel_pos_parameter g p hs _ hY).ne'
  have he:=extractionQ_standardized_normalizer_exact g p k x hh hk hx hsaddle
  have hden:(Real.pi*extractionQ g p k/markedModel g p 0)*x^k*
      Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)=
      (markedModel g p (inverseY x)/markedModel g p 0)*(poissonCenter k*Real.sqrt (k:ℝ)):=by
    calc
      _=(Real.pi/markedModel g p 0)*
        (extractionQ g p k*x^k*Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)):=by ring
      _=_:=by rw[he];field_simp [Real.pi_ne_zero,hM0]
  have hdenC:(x:ℂ)^k*(Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):ℂ)*
      ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)=
      ((markedModel g p (inverseY x)/markedModel g p 0:ℝ):ℂ)*
        ((poissonCenter k*Real.sqrt (k:ℝ):ℝ):ℂ):=by
    have hc:=congrArg Complex.ofReal hden
    push_cast at hc ⊢
    convert hc using 1 <;>ring
  rw[hdenC]
  exact mul_div_mul_left _ _ (by exact_mod_cast div_ne_zero hMY hM0)

lemma marked_model_saddle_prefactor_bound_nonTiny (κ:ℝ)(hκ:0<κ):
    ∃H:ℝ,0<H ∧ ∀g p k:ℕ,H≤(complexity g p:ℝ)→
      κ*Real.sqrt (complexity g p:ℝ)≤(k:ℝ)→Stable g p→
      ∀x∈Ioo (0:ℝ) xCritical,(k:ℝ)=(complexity g p:ℝ)*WP.Psi x→
      ∀z:ℂ,‖z‖≤2→
      let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
      let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
      ‖(((markedModel g p (inverseY x)/markedModel g p 0:ℝ):ℂ)*z)/
        ((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))‖≤4*Real.sqrt (2*Real.pi):=by
  obtain ⟨H0,hH0,hnum⟩:=poissonNormalizer_nonTiny_window κ hκ
  obtain ⟨H1,hH1,hbound⟩:=poisson_central_factor_bound_nonTiny κ hκ
  let H:ℝ:=max H0 H1
  have hH:0<H:=hH0.trans_le (le_max_left _ _)
  refine ⟨H,hH,?_⟩
  intro g p k hg hk hs x hx hroot z hz
  have hh:0<(complexity g p:ℝ):=hH.trans_le hg
  have hg0:H0≤(complexity g p:ℝ):=(le_max_left _ _).trans hg
  have hg1:H1≤(complexity g p:ℝ):=(le_max_right _ _).trans hg
  have hk1:1≤k:=(hnum _ hg0 k hk).1
  dsimp only
  rw[marked_model_saddle_prefactor_exact g p k hs x hh hk1 hx hroot z]
  exact hbound _ hg1 k hk z hz
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma normalizedMarkedGenerating_saddle_prefactor_exact (P:PsiTheory)(g p k:ℕ)(hs:Stable g p)(x:ℝ)
    (hh:0<(complexity g p:ℝ))(hk:1≤k)(hx:x∈Ioo (0:ℝ) xCritical)
    (hsaddle:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x):
    let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
    let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
    HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)/
      ((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))=
      ((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)/
        ((poissonCenter k*Real.sqrt (k:ℝ):ℝ):ℂ):=by
  dsimp only
  have hY:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hMY:markedModel g p (inverseY x)≠0:=(markedModel_pos_parameter g p hs _ hY).ne'
  have hm:(markedModel g p (inverseY x)/markedModel g p 0)*
      (Real.pi*markedF P g p x/markedModel g p (inverseY x))=
      Real.pi*markedF P g p x/markedModel g p 0:=by field_simp
  have he:=marked_model_saddle_prefactor_exact g p k hs x hh hk hx hsaddle
    ((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)
  rw[←Complex.ofReal_mul,hm] at he
  rw[HigherOrder.normalizedMarkedGenerating_real P g p hs x ⟨hx.1.le,hx.2⟩]
  exact he

lemma normalizedMarkedGenerating_saddle_prefactor_bound_nonTiny (κ:ℝ)(hκ:0<κ):
    ∃H:ℝ,0<H ∧ ∀(P:PsiTheory)(g p k:ℕ),H≤(complexity g p:ℝ)→
      κ*Real.sqrt (complexity g p:ℝ)≤(k:ℝ)→Stable g p→
      ∀x∈Ioo (0:ℝ) xCritical,(k:ℝ)=(complexity g p:ℝ)*WP.Psi x→
      ∀z:ℂ,z≠0→‖z‖≤2→
      ‖((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)/z-1‖≤1/2→
      let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
      let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
      ‖HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)/
        ((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))‖≤6*Real.sqrt (2*Real.pi):=by
  obtain ⟨H,hH,hnum⟩:=poissonNormalizer_nonTiny_window κ hκ
  refine ⟨H,hH,?_⟩
  intro P g p k hg hk hs x hx hroot z hzne hz he
  have hh:0<(complexity g p:ℝ):=hH.trans_le hg
  have ht:=hnum _ hg k hk
  have hkpos:0<(k:ℝ):=by exact_mod_cast (show 0<k by omega)
  have hpc:0<poissonCenter k:=by unfold poissonCenter;positivity
  have hden:0<poissonCenter k*Real.sqrt (k:ℝ):=mul_pos hpc (Real.sqrt_pos.mpr hkpos)
  let F:ℂ:=((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)
  have heF:‖F/z-1‖≤1/2:=he
  have hrel:‖F/z‖≤3/2:=by
    calc
      _=‖(F/z-1)+1‖:=by congr 1;ring
      _≤‖F/z-1‖+‖(1:ℂ)‖:=norm_add_le _ _
      _≤3/2:=by simp only[norm_one];linarith only[heF]
  have hF:‖F‖≤3:=by
    have hc:F=(F/z)*z:=by rw[div_mul_cancel₀ _ hzne]
    rw[hc,norm_mul]
    calc
      _≤(3/2:ℝ)*2:=mul_le_mul hrel hz (norm_nonneg z) (by norm_num:(0:ℝ)≤3/2)
      _=3:=by norm_num
  dsimp only
  rw[normalizedMarkedGenerating_saddle_prefactor_exact P g p k hs x hh ht.1 hx hroot,
    norm_div,Complex.norm_of_nonneg hden.le,div_eq_mul_inv]
  apply (mul_le_mul hF ht.2.2.2 (inv_nonneg.mpr hden.le) (by norm_num:(0:ℝ)≤3)).trans_eq
  ring
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma normalizedMarkedGenerating_saddle_prefactor_difference_nonTiny (κ:ℝ)(hκ:0<κ):
    ∃H:ℝ,0<H ∧ ∀(P:PsiTheory)(g p k:ℕ),H≤(complexity g p:ℝ)→
      κ*Real.sqrt (complexity g p:ℝ)≤(k:ℝ)→Stable g p→
      ∀x∈Ioo (0:ℝ) xCritical,(k:ℝ)=(complexity g p:ℝ)*WP.Psi x→
      ∀(z:ℂ)(ε:ℝ),z≠0→‖z‖≤2→0≤ε→
      ‖((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)/z-1‖≤ε→
      let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
      let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
      ‖HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))-
        (((markedModel g p (inverseY x)/markedModel g p 0:ℝ):ℂ)*z)/
          ((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))‖≤(4*Real.sqrt (2*Real.pi))*ε:=by
  obtain ⟨H,hH,hbound⟩:=marked_model_saddle_prefactor_bound_nonTiny κ hκ
  refine ⟨H,hH,?_⟩
  intro P g p k hg hk hs x hx hroot z ε hzne hz hε he
  have hh:0<(complexity g p:ℝ):=hH.trans_le hg
  have hkpos:0<(k:ℝ):=(mul_pos hκ (Real.sqrt_pos.mpr hh)).trans_le hk
  have hk1:1≤k:=by exact_mod_cast (show 0<k by exact_mod_cast hkpos)
  have hpc:0<poissonCenter k:=by unfold poissonCenter;positivity
  let d:ℂ:=((poissonCenter k*Real.sqrt (k:ℝ):ℝ):ℂ)
  let F:ℂ:=((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)
  have hdn:d≠0:=by
    dsimp only[d]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hpc (Real.sqrt_pos.mpr hkpos)).ne'
  have hb:‖z/d‖≤4*Real.sqrt (2*Real.pi):=by
    have ht:=hbound g p k hg hk hs x hx hroot z hz
    dsimp only at ht
    rw[marked_model_saddle_prefactor_exact g p k hs x hh hk1 hx hroot z] at ht
    exact ht
  have heF:‖F/z-1‖≤ε:=he
  have hid:F/d-z/d=(z/d)*(F/z-1):=by
    field_simp [hzne,hdn] <;>ring
  dsimp only
  rw[normalizedMarkedGenerating_saddle_prefactor_exact P g p k hs x hh hk1 hx hroot,
    marked_model_saddle_prefactor_exact g p k hs x hh hk1 hx hroot z]
  change ‖F/d-z/d‖≤_
  rw[hid,norm_mul]
  exact mul_le_mul hb heF (norm_nonneg _) (by positivity)
end WP.Analysis
