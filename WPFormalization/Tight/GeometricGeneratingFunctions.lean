import WPFormalization.Tight.CuspSpecialization
/-! Actual protected-tight WP generating functions. The exact Appendix F.1
identity and convergence include every stable pair, including p=0. The
uniform profile bounds and positive factor below are proved for p>=1;
the original unmarked positive-factor claim remains a separate obligation.
The only new external premise is the source-verified generic classical
Budd--Zonneveld transform, with the genuine geometric tight locus. -/
noncomputable section
namespace WP
open Set Filter MeasureTheory External TightMoments PositiveConvolution
open scoped Topology

def tightGeneratingFunction {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (g p:ℕ) (L:Fin p→ℝ) (x:ℝ):ℝ:=
  ∑'k:ℕ,tightVolume T g p k L (fun _=>0)/
    ((2*Real.pi^2)^(dimension g p+k)*(k.factorial:ℝ))*x^k

lemma tightGeneratingFunction_hasSum {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (B:BuddZonneveldTransform G T)
    (g p:ℕ) (hs:Stable g p) (L:Fin p→ℝ) (hL:∀i,0≤L i)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    HasSum (fun k:ℕ=>tightVolume T g p k L (fun _=>0)/
      ((2*Real.pi^2)^(dimension g p+k)*(k.factorial:ℝ))*x^k)
      (tightShiftedPolynomial P g p (inverseY x) L):=by
  have hnorm:‖(x:ℂ)‖<xCritical:=by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have ht:=(momentTightG_taylor P g p L (x:ℂ) hnorm).mapL Complex.reCLM
  convert ht using 1
  · ext k
    rw [geometric_tight_cusp_coefficient T B g p hs L hL k]
    simp only [Complex.reCLM_apply,←Complex.ofReal_pow,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]
  · rw [momentTightG_ofReal P g p L x hx]
    rfl

@[blueprint "lem:tight-gf"]
lemma tightGeneratingFunction_identity {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (B:BuddZonneveldTransform G T)
    (g p:ℕ) (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀)
    (L:Fin p→ℝ) (hL:∀i,0≤L i):
    tightGeneratingFunction T g p L (XR Y)=tightShiftedPolynomial P g p Y L:=by
  have hx:XR Y∈Ico (0:ℝ) xCritical:=⟨XR_nonneg_interior Y hY,
    XR_strictMonoOn (show Y∈Iic y₀ from hY.2.le) (by simp) hY.2⟩
  have hi:inverseY (XR Y)=Y:=Analysis.inverseY_eq_of_root _ _ hY.2.le rfl
  simpa only [tightGeneratingFunction,hi] using (tightGeneratingFunction_hasSum T B g p hs L hL (XR Y) hx).tsum_eq

lemma tightGeneratingFunction_bounds {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (B:BuddZonneveldTransform G T)
    (g p:ℕ) (hp:1≤p) (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀)
    (L:Fin p→ℝ) (hL:∀i,0≤L i):
    1≤tightGeneratingFunction T g p L (XR Y)/shifted P g (List.replicate p 0) Y ∧
    tightGeneratingFunction T g p L (XR Y)/shifted P g (List.replicate p 0) Y≤
      ∏i,boundaryFactor 0 (tightParameterScale Y*L i):=by
  rw [tightGeneratingFunction_identity T B g p hs Y hY L hL]
  exact tightShiftedPolynomial_bounds P g p hp hs Y hY L

lemma tightGeneratingFunction_uniform_relative_error {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T) (p:ℕ) (hp:1≤p)
    (B:ℝ) (hB:0≤B):
    ∃C:ℝ,0<C ∧ ∀g:ℕ,1≤g→∀Y∈Ico (0:ℝ) y₀,∀L:Fin p→ℝ,
      (∀i,0≤L i)→(∀i,tightParameterScale Y*L i≤B)→
      |tightGeneratingFunction T g p L (XR Y)/
        (shifted P g (List.replicate p 0) Y*
          ∏i,boundaryFactor 0 (tightParameterScale Y*L i))-1|≤C/(g:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=tightShiftedPolynomial_uniform_relative_error P p hp B hB
  refine ⟨C,hC,?_⟩
  intro g hg Y hY L hL hLU
  have hs:Stable g p:=by unfold Stable;omega
  rw [tightGeneratingFunction_identity T BZ g p hs Y hY L hL]
  exact hbound g hg Y hY L hL hLU

lemma tightGeneratingFunction_positive_factor {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (B:BuddZonneveldTransform G T)
    (g p:ℕ) (hp:1≤p) (hs:Stable g p) (L:Fin p→ℝ) (hL:∀i,0≤L i)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    (tightGeneratingFunction T g p L x:ℂ)=
      universalV P (x:ℂ)^(complexity g p)*TightConvolution.tightR P g p L (x:ℂ):=by
  have he: tightGeneratingFunction T g p L x=tightShiftedPolynomial P g p (inverseY x) L:=
    (tightGeneratingFunction_hasSum T B g p hs L hL x hx).tsum_eq
  rw [he,←momentTightG_ofReal P g p L x hx]
  apply momentTightG_eq_positive_factor P g p hp hs L
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
end WP
