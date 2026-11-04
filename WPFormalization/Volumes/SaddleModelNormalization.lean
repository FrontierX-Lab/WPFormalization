import WPFormalization.Volumes.OriginFiniteModel
import WPFormalization.Volumes.TransportPrimitive
/-! Exact positive-saddle normalization of the actual extractionQ and the given finite marked model. The physical saddle and original density inverse are identified before cancelling factors. No asymptotic comparison is assumed. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma densityY_at_positive_saddle (g p k:ℕ)(x:ℝ)(hh:0<(complexity g p:ℝ))
    (hk:1≤k)(hx:x∈Ioo (0:ℝ) xCritical)
    (hsaddle:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x):
    densityY (2*(k:ℝ)/(complexity g p:ℝ))=inverseY x:=by
  have hkpos:0<(k:ℝ):=by exact_mod_cast (show 0<k by omega)
  have hrho:0<2*(k:ℝ)/(complexity g p:ℝ):=by positivity
  have hd:=densityY_spec (2*(k:ℝ)/(complexity g p:ℝ)) hrho.le
  have hY:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  apply density_strictMonoOn.injOn hd.1 hY
  rw[hd.2]
  have hν:(k:ℝ)/(complexity g p:ℝ)=WP.Psi x:=(div_eq_iff hh.ne').mpr (by simpa only[mul_comm] using hsaddle)
  calc
    _=2*((k:ℝ)/(complexity g p:ℝ)):=by ring
    _=2*WP.Psi x:=by rw[hν]
    _=WP.density (inverseY x):=by unfold WP.Psi;ring

lemma extractionQ_at_positive_saddle (g p k:ℕ)(x:ℝ)(hh:0<(complexity g p:ℝ))
    (hk:1≤k)(hx:x∈Ioo (0:ℝ) xCritical)
    (hsaddle:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x):
    extractionQ g p k=markedModel g p (inverseY x)/Real.pi*
      (x⁻¹^k*poissonCenter k*Real.sqrt ((k:ℝ)/((complexity g p:ℝ)*WP.euler WP.Psi x))):=by
  have hY:=densityY_at_positive_saddle g p k x hh hk hx hsaddle
  simp only[extractionQ,hY,(inverseY_branch x ⟨hx.1.le,hx.2⟩).2,
    show k≠0 by omega,ite_false]

lemma extractionQ_standardized_normalizer_exact (g p k:ℕ)(x:ℝ)(hh:0<(complexity g p:ℝ))
    (hk:1≤k)(hx:x∈Ioo (0:ℝ) xCritical)
    (hsaddle:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x):
    extractionQ g p k*x^k*Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)=
      markedModel g p (inverseY x)/Real.pi*poissonCenter k*Real.sqrt (k:ℝ):=by
  have hv:0<WP.euler WP.Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hσ:0<Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):=Real.sqrt_pos.mpr (mul_pos hh hv)
  have hsr:Real.sqrt ((k:ℝ)/((complexity g p:ℝ)*WP.euler WP.Psi x))*
      Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)=Real.sqrt (k:ℝ):=by
    rw[Real.sqrt_div (Nat.cast_nonneg k),div_mul_cancel₀ _ hσ.ne']
  calc
    _=markedModel g p (inverseY x)/Real.pi*poissonCenter k*
        (Real.sqrt ((k:ℝ)/((complexity g p:ℝ)*WP.euler WP.Psi x))*Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x))*
          (x⁻¹^k*x^k):=by rw[extractionQ_at_positive_saddle g p k x hh hk hx hsaddle];ring
    _=_:=by rw[←mul_pow,inv_mul_cancel₀ hx.1.ne',one_pow,hsr,mul_one]

lemma normalizedFiniteMarkedModel_at_physical (P:PsiTheory)(g p J:ℕ)(hs:Stable g p)
    (S Bc:ℂ→ℂ)(f:ℕ→ℂ→ℂ)(x:ℝ)(hx:x∈Ico (0:ℝ) xCritical)
    (hS:S (x:ℂ)=(extractionS x:ℂ))(hBc:Bc (x:ℂ)=(extractionB p x:ℂ)):
    HigherOrder.normalizedFiniteMarkedModel P g p S Bc f J (x:ℂ)=
      ((markedModel g p (inverseY x)/markedModel g p 0:ℝ):ℂ)*
        HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J (inverseY x:ℂ):=by
  have hY:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x hx).1
  have hf:=extraction_factorization_proof g p (inverseY x) hY
  rw[(inverseY_branch x hx).2] at hf
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hm:markedModel g p (inverseY x)/markedModel g p 0=
      Real.exp ((complexity g p:ℝ)*extractionS x)*extractionB p x:=by
    rw[hf]
    field_simp
  unfold HigherOrder.normalizedFiniteMarkedModel
  rw[hS,hBc,PositiveConvolution.planarInverse_ofReal P x hx]
  rw[←Complex.ofReal_natCast,←Complex.ofReal_mul,←Complex.ofReal_exp,←Complex.ofReal_mul,hm]

lemma normalized_model_saddle_prefactor_exact (P:PsiTheory)(g p k J:ℕ)(hs:Stable g p)
    (S Bc:ℂ→ℂ)(f:ℕ→ℂ→ℂ)(x:ℝ)(hh:0<(complexity g p:ℝ))
    (hk:1≤k)(hx:x∈Ioo (0:ℝ) xCritical)
    (hsaddle:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x)
    (hS:S (x:ℂ)=(extractionS x:ℂ))(hBc:Bc (x:ℂ)=(extractionB p x:ℂ)):
    let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
    let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
    HigherOrder.normalizedFiniteMarkedModel P g p S Bc f J (x:ℂ)/
      ((x:ℂ)^k*(σ:ℂ)*(Qn:ℂ))=
      HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J (inverseY x:ℂ)/
        ((poissonCenter k*Real.sqrt (k:ℝ):ℝ):ℂ):=by
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
  rw[normalizedFiniteMarkedModel_at_physical P g p J hs S Bc f x ⟨hx.1.le,hx.2⟩ hS hBc,hdenC]
  exact mul_div_mul_left _ _ (by exact_mod_cast div_ne_zero hMY hM0)
end WP.Analysis
