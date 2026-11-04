import WPFormalization.Tight.GeometricGeneratingFunctions
import WPFormalization.Tight.UnmarkedKappaFactor
/-! Appendix F.1: the actual tight generating functions at every stable pair.

The identity, profile bounds, uniform error, and convergent positive factor
include the unmarked branch. Every classical input remains explicit.
-/
noncomputable section
namespace WP
open Set Filter External TightMoments TightUnmarked PositiveConvolution
open scoped Topology
universe u v
/-- The actual positive analytic factor: the unmarked branch uses the finite
higher-kappa polynomial; protected branches use the shifted recursion. -/
def tightPositiveFactor (C : HigherKappaRealization.{u} P) (g p : ℕ)
    (L : Fin p→ℝ) (z : ℂ) : ℂ :=
  if p=0 then unmarkedR C g z else TightConvolution.tightR P g p L z
lemma tightPositiveFactor_analyticAt (C : HigherKappaRealization.{u} P) (g p : ℕ)
    (L : Fin p→ℝ) (z : ℂ) (hz : ‖z‖<xCritical) :
    AnalyticAt ℂ (tightPositiveFactor C g p L) z := by
  unfold tightPositiveFactor
  split_ifs
  · exact unmarkedR_analyticAt C g z hz
  · exact TightConvolution.tightR_analyticAt P g p L z hz
lemma tightPositiveFactor_positiveJets (C : HigherKappaRealization.{u} P) (g p : ℕ)
    (hs : Stable g p) (L : Fin p→ℝ) : PositiveJets (tightPositiveFactor C g p L) := by
  unfold tightPositiveFactor
  split_ifs with hp
  · subst p
    exact unmarkedR_positiveJets C g hs
  · exact TightConvolution.tightR_positiveJets P g p L
lemma tightPositiveFactor_taylor (C : HigherKappaRealization.{u} P) (g p : ℕ)
    (L : Fin p→ℝ) (z : ℂ) (hz : ‖z‖<xCritical) :
    HasSum (fun j=>WP.coeff (tightPositiveFactor C g p L) j*z^j)
      (tightPositiveFactor C g p L z) :=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (tightPositiveFactor_analyticAt C g p L) z hz
lemma tightPositiveFactor_real_nonnegative_coefficients
    (C : HigherKappaRealization.{u} P) (g p : ℕ) (hs : Stable g p) (L : Fin p→ℝ) :
    ∀j,0≤realCoeff (tightPositiveFactor C g p L) j ∧
      (WP.coeff (tightPositiveFactor C g p L) j).im=0 :=
  (tightPositiveFactor_positiveJets C g p hs L).coefficient_nonneg
lemma momentTightG_allStable_positive_factor (C : HigherKappaRealization.{u} P)
    (g p : ℕ) (hs : Stable g p) (L : Fin p→ℝ) (z : ℂ) (hz : ‖z‖<xCritical) :
    momentTightG P g p L z=universalV P z^(complexity g p)*tightPositiveFactor C g p L z := by
  by_cases hp:p=0
  · subst p
    simp only [tightPositiveFactor,ite_true]
    exact momentTightG_unmarked_factor C g (by unfold Stable at hs;omega) L z hz
  · simp only [tightPositiveFactor,ite_eq_right hp]
    exact momentTightG_eq_positive_factor P g p (by omega) hs L z hz
lemma tightShiftedPolynomial_allStable_bounds (C : HigherKappaRealization.{u} P)
    (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y∈Ico (0:ℝ) y₀) (L : Fin p→ℝ) :
    1≤tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y ∧
    tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y≤
      ∏i,boundaryFactor 0 (tightParameterScale Y*L i) := by
  by_cases hp:p=0
  · subst p
    have hg:2≤g := by unfold Stable at hs;omega
    have hpos:shifted P g [] Y≠0 := (shifted_unmarked_positive C g hg Y hY).ne'
    simp [tightShiftedPolynomial_zero,hpos]
  · exact tightShiftedPolynomial_bounds P g p (by omega) hs Y hY L
lemma tightShiftedPolynomial_allStable_uniform_relative_error
    (C : HigherKappaRealization.{u} P) (p : ℕ) (B : ℝ) (hB : 0≤B) :
    ∃K:ℝ,0<K ∧ ∀g:ℕ,1≤g→Stable g p→∀Y∈Ico (0:ℝ) y₀,∀L:Fin p→ℝ,
      (∀i,0≤L i)→(∀i,tightParameterScale Y*L i≤B)→
      |tightShiftedPolynomial P g p Y L/
        (shifted P g (List.replicate p 0) Y*
          ∏i,boundaryFactor 0 (tightParameterScale Y*L i))-1|≤K/(g:ℝ) := by
  by_cases hp:p=0
  · subst p
    refine ⟨1,zero_lt_one,?_⟩
    intro g hg hs Y hY L hL hLB
    have hg':2≤g := by unfold Stable at hs;omega
    have hpos:shifted P g [] Y≠0 := (shifted_unmarked_positive C g hg' Y hY).ne'
    simp [tightShiftedPolynomial_zero,hpos]
  · obtain ⟨K,hK,hbound⟩:=tightShiftedPolynomial_uniform_relative_error P p (by omega) B hB
    exact ⟨K,hK,fun g hg hs=>hbound g hg⟩

@[blueprint "lem:tight-gf"]
lemma tightGeneratingFunction_allStable_bounds {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T) (C:HigherKappaRealization P)
    (g p:ℕ) (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀)
    (L:Fin p→ℝ) (hL:∀i,0≤L i):
    1≤tightGeneratingFunction T g p L (XR Y)/shifted P g (List.replicate p 0) Y ∧
    tightGeneratingFunction T g p L (XR Y)/shifted P g (List.replicate p 0) Y≤
      ∏i,boundaryFactor 0 (tightParameterScale Y*L i) := by
  rw [tightGeneratingFunction_identity T BZ g p hs Y hY L hL]
  exact tightShiftedPolynomial_allStable_bounds C g p hs Y hY L
@[blueprint "lem:tight-gf"]
lemma tightGeneratingFunction_allStable_uniform_relative_error
    {P:PsiTheory} {G:WeilPeterssonGeometry P} (T:TightRegions G)
    (BZ:BuddZonneveldTransform G T) (C:HigherKappaRealization P)
    (p:ℕ) (B:ℝ) (hB:0≤B):
    ∃K:ℝ,0<K ∧ ∀g:ℕ,1≤g→Stable g p→∀Y∈Ico (0:ℝ) y₀,∀L:Fin p→ℝ,
      (∀i,0≤L i)→(∀i,tightParameterScale Y*L i≤B)→
      |tightGeneratingFunction T g p L (XR Y)/
        (shifted P g (List.replicate p 0) Y*
          ∏i,boundaryFactor 0 (tightParameterScale Y*L i))-1|≤K/(g:ℝ) := by
  obtain ⟨K,hK,hbound⟩:=tightShiftedPolynomial_allStable_uniform_relative_error C p B hB
  refine ⟨K,hK,?_⟩
  intro g hg hs Y hY L hL hLB
  rw [tightGeneratingFunction_identity T BZ g p hs Y hY L hL]
  exact hbound g hg hs Y hY L hL hLB
@[blueprint "lem:tight-gf"]
lemma tightGeneratingFunction_allStable_positive_factor
    {P:PsiTheory} {G:WeilPeterssonGeometry P} (T:TightRegions G)
    (BZ:BuddZonneveldTransform G T) (C:HigherKappaRealization P)
    (g p:ℕ) (hs:Stable g p) (L:Fin p→ℝ) (hL:∀i,0≤L i)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    (tightGeneratingFunction T g p L x:ℂ)=
      universalV P (x:ℂ)^(complexity g p)*tightPositiveFactor C g p L (x:ℂ) := by
  have he:tightGeneratingFunction T g p L x=tightShiftedPolynomial P g p (inverseY x) L :=
    (tightGeneratingFunction_hasSum T BZ g p hs L hL x hx).tsum_eq
  rw [he,←momentTightG_ofReal P g p L x hx]
  apply momentTightG_allStable_positive_factor C g p hs L
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
lemma tightGeneratingFunction_allStable_marked_bounds
    {P:PsiTheory} {G:WeilPeterssonGeometry P} (T:TightRegions G)
    (BZ:BuddZonneveldTransform G T) (C:HigherKappaRealization P)
    (g p:ℕ) (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀)
    (L:Fin p→ℝ) (hL:∀i,0≤L i):
    1≤tightGeneratingFunction T g p L (XR Y)/markedF P g p (XR Y) ∧
    tightGeneratingFunction T g p L (XR Y)/markedF P g p (XR Y)≤
      ∏i,boundaryFactor 0 (tightParameterScale Y*L i) := by
  rw [←string_flow_proof P g p hs Y hY]
  exact tightGeneratingFunction_allStable_bounds T BZ C g p hs Y hY L hL
lemma Phi_unmarked_real_positive_factor (C:HigherKappaRealization.{u} P)
    (g:ℕ) (hg:2≤g) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    Phi P g (x:ℂ)=universalV P (x:ℂ)^(complexity g 0)*unmarkedR C g (x:ℂ) := by
  have hs:Stable g 0 := by unfold Stable;omega
  have hy:=inverseY_branch x hx
  have hf:=string_flow_proof P g 0 hs (inverseY x) hy.1
  rw [hy.2] at hf
  have him:=Phi_iteratedDeriv_real P g 0 x (by simpa only [abs_of_nonneg hx.1] using hx.2)
  have he:Phi P g (x:ℂ)=(shifted P g [] (inverseY x):ℂ) := by
    apply Complex.ext
    · simpa only [List.replicate_zero,markedF,iteratedDeriv_zero,Complex.ofReal_re] using hf.symm
    · simpa only [iteratedDeriv_zero,Complex.ofReal_im] using him
  rw [he,unmarkedG_ofReal C g hg x hx]
lemma Phi_unmarked_positive_factor (C:HigherKappaRealization.{u} P)
    (g:ℕ) (hg:2≤g) (z:ℂ) (hz:‖z‖<xCritical):
    Phi P g z=universalV P z^(complexity g 0)*unmarkedR C g z := by
  have hf:AnalyticOnNhd ℂ (Phi P g) (Metric.ball 0 xCritical) := by
    intro w hw
    exact Phi_analyticAt_open_disk P g w
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hq:AnalyticOnNhd ℂ (fun w=>universalV P w^(complexity g 0)*unmarkedR C g w)
      (Metric.ball 0 xCritical) := by
    intro w hw
    have hw':‖w‖<xCritical := by simpa only [Metric.mem_ball,dist_zero_right] using hw
    have hv:AnalyticAt ℂ (universalV P) w := by
      change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) w
      simpa only [iteratedDeriv_eq_iterate] using
        (Phi_analyticAt_open_disk P 0 w hw').iterated_deriv 3
    exact (hv.pow _).mul (unmarkedR_analyticAt C g w hw')
  have hc:xCritical/2∈Ioo (0:ℝ) xCritical :=
    ⟨half_pos Analysis.xCritical_pos_parameter,half_lt_self Analysis.xCritical_pos_parameter⟩
  have hmem:((xCritical/2:ℝ):ℂ)∈Metric.ball 0 xCritical := by
    simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hc.1.le] using hc.2
  have he:EqOn (Phi P g) (fun w=>universalV P w^(complexity g 0)*unmarkedR C g w)
      (Metric.ball 0 xCritical) := by
    apply Analysis.complex_identity_of_real_germ _ _ _ (xCritical/2) hf hq
      (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx
    exact Phi_unmarked_real_positive_factor C g hg x ⟨hx.1.le,hx.2⟩
  exact he (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
end WP
