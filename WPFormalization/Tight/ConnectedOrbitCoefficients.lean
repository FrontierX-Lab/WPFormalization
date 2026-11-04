import WPFormalization.Tight.ConnectedOrbitCutData
import WPFormalization.Tight.ConnectedOriginal
import WPFormalization.Tight.SeparatingPhysicalKernel
import WPFormalization.Analysis.CoefficientSubstitution
import WPFormalization.Critical.SurvivingMixedVolume
noncomputable section
namespace WP.TightConnected
open Set Filter Finset External MeasureTheory
open scoped Topology BigOperators ENNReal
lemma momentTightG_coeff_polynomial (P : PsiTheory) (g p n : ℕ) (L : Fin p→ℝ) :
    WP.coeff (TightMoments.momentTightG P g p L) n =
      ∑d∈degreeTuples g p,
        (∏i,(L i:ℂ)^(2*d i)/((2:ℂ)^(d i)*(d i).factorial))*
        WP.coeff (fun z=>TightMoments.complexMomentAmplitude P g (List.ofFn d)
          (fun j=>TightMoments.scaledPlaneMoments P j z)/(2*Real.pi^2:ℝ)^(dimension g p)) n := by
  classical
  let A : (Fin p→ℕ)→ℂ→ℂ := fun d z=>
    TightMoments.complexMomentAmplitude P g (List.ofFn d)
      (fun j=>TightMoments.scaledPlaneMoments P j z)/(2*Real.pi^2:ℝ)^(dimension g p)
  have ha (d : Fin p→ℕ) : AnalyticAt ℂ (A d) 0 := by
    apply AnalyticAt.div_const
    apply TightMoments.complexMomentAmplitude_analyticAt
    · intro j
      exact TightMoments.scaledPlaneMoments_analyticAt P j 0
        (by simpa using Analysis.xCritical_pos_parameter)
    · rw [TightMoments.scaledPlaneMoments_zero_index]
      exact PositiveConvolution.derivX_planarInverse_ne_zero P 0
        (by simpa using Analysis.xCritical_pos_parameter)
  have he : TightMoments.momentTightG P g p L = fun z=>∑d∈degreeTuples g p,
      (∏i,(L i:ℂ)^(2*d i)/((2:ℂ)^(d i)*(d i).factorial))*A d z := by
    funext z
    unfold TightMoments.momentTightG TightMoments.complexMomentPolynomial
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [A]
    ring
  rw [he,Analysis.coeff_finite_sum (degreeTuples g p)
    (fun d z=>(∏i,(L i:ℂ)^(2*d i)/((2:ℂ)^(d i)*(d i).factorial))*A d z)
    (fun d hd=>(analyticAt_const.mul (ha d))) n]
  simp only [Analysis.coeff_const_mul,A]

lemma momentTightG_realCoeff_continuous (P : PsiTheory) (g p n : ℕ) :
    Continuous (fun L : Fin p→ℝ=>realCoeff (TightMoments.momentTightG P g p L) n) := by
  simp only [realCoeff,momentTightG_coeff_polynomial]
  fun_prop

lemma connected_cut_kernel_volume_ratio {P : PsiTheory} {G : WeilPeterssonGeometry P}
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T) (g k n : ℕ)
    (D : MulticurveCutData 0 k) (hc : D.components=1) (hg : 2≤g)
    (hs : ∀c,Stable (D.genus c) (D.boundaryCount c))
    (heuler : (∑c,D.genus c)+k+1=g+D.components)
    (c : Fin D.components) (x : Fin k→ℝ) (hx : ∀i,0≤x i) :
    D.tightCutKernel T (fun i=>Fin.elim0 i) (fun _ : Fin n=>0) x / cuspVolume G g n =
      (realCoeff (TightMoments.momentTightG P (g-k) (2*k)
        (connected_cut_boundaryVector k D hc c x)) n/realCoeff (Phi P g) n)/(2*Real.pi^2)^k := by
  have hL : ∀j,0≤D.tightProtectedLengths (fun i=>Fin.elim0 i) x c j := by
    intro j
    rw [connected_cut_boundary_length k D hc c x]
    exact hx _
  have hcoeff := TightMoments.geometric_tight_cusp_coefficient T BZ (D.genus c)
    (D.boundaryCount c) (hs c) _ hL n
  rw [connected_cut_genus g k D hc heuler c,
    momentTightG_finCongr P (g-k) _ _ (connected_cut_boundaryCount k D hc c)] at hcoeff
  have hdim := TightSeparating.tight_cut_dimension_budget g k D hs heuler hg
  have hsingle : (∑i,dimension (D.genus i) (D.boundaryCount i))=
      dimension (D.genus c) (D.boundaryCount c) := by
    rcases D with ⟨q,gen,cv,ev⟩
    dsimp at hc
    subst q
    have hc0 : c=0 := Subsingleton.elim _ _
    subst c
    exact Fin.sum_univ_one _
  rw [hsingle] at hdim
  have he : dimension g 0+n=k+(dimension (D.genus c) (D.boundaryCount c)+n) := by omega
  have hnorm :
      D.tightCutKernel T (fun i=>Fin.elim0 i) (fun _ : Fin n=>0) x /
        ((2*Real.pi^2)^(dimension g 0+n)*(n.factorial : ℝ)) =
      realCoeff (TightMoments.momentTightG P (g-k) (2*k)
        (connected_cut_boundaryVector k D hc c x)) n/(2*Real.pi^2)^k := by
    rw [connected_cut_kernel_single T k n D hc c x,he,pow_add,
      connected_cut_genus g k D hc heuler c]
    change _ = realCoeff (TightMoments.momentTightG P (g-k) (2*k)
      (fun j=>D.tightProtectedLengths (fun i=>Fin.elim0 i) x c
        ((finCongr (connected_cut_boundaryCount k D hc c)).symm j))) n/(2*Real.pi^2)^k
    rw [←hcoeff]
    ring
  have hdn : dimension g n=dimension g 0+n := by unfold dimension;omega
  have hV : cuspVolume G g n =
      ((2*Real.pi^2)^(dimension g 0+n)*(n.factorial : ℝ))*realCoeff (Phi P g) n := by
    rw [Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega),
      TightSeparating.unmarked_realCoeff_volume,hdn]
    field_simp
  rw [hV,div_mul_eq_div_div,hnorm]
  ring

def connectedCutScaledCoefficientDensity (P : PsiTheory) (k g n : ℕ)
    (D : MulticurveCutData 0 k) (hc : D.components=1) (c : Fin D.components)
    (x : Fin k→ℝ) : ℝ :=
  (realCoeff (TightMoments.momentTightG P (g-k) (2*k)
    (fun j=>connected_cut_boundaryVector k D hc c x j/tightScale ((n:ℝ)/(g:ℝ)))) n/
    realCoeff (Phi P g) n)/
    ((2*Real.pi^2)^k*(tightScale ((n:ℝ)/(g:ℝ)))^(2*k)*(2:ℝ)^k)*∏i,x i

lemma connected_cut_boundaryVector_continuous (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) :
    Continuous (connected_cut_boundaryVector k D hc c) := by
  apply continuous_pi
  intro j
  simp only [connected_cut_boundaryVector,connected_cut_boundary_length k D hc c]
  exact continuous_apply _

lemma connected_cut_scaled_coefficient_density_continuous (P : PsiTheory) (k g n : ℕ)
    (D : MulticurveCutData 0 k) (hc : D.components=1) (c : Fin D.components) :
    Continuous (connectedCutScaledCoefficientDensity P k g n D hc c) := by
  unfold connectedCutScaledCoefficientDensity
  apply Continuous.mul
  · apply Continuous.div_const
    apply Continuous.div_const
    apply (momentTightG_realCoeff_continuous P (g-k) (2*k) n).comp
    apply continuous_pi
    intro j
    exact ((continuous_apply j).comp (connected_cut_boundaryVector_continuous k D hc c)).div_const _
  · fun_prop

lemma connected_cut_scaled_coefficient_density_eq_ratio (P : PsiTheory) (k g n : ℕ)
    (D : MulticurveCutData 0 k) (hc : D.components=1) (c : Fin D.components)
    (x : Fin k→ℝ) :
    connectedCutScaledCoefficientDensity P k g n D hc c x =
      connectedDensityCoefficientRatio P k g n (connected_cut_boundaryVector k D hc c x) *
        ∏i,tightIntensityDensity (x i) := by
  let Y := densityY ((n:ℝ)/(g:ℝ))
  have hY : Y∈Ico (0:ℝ) y₀ := (Analysis.densityY_spec _ (by positivity)).1
  have ha : 0<tightScale ((n:ℝ)/(g:ℝ)) := tightScale_pos _ (by positivity)
  have hr : 0<r Y := r_pos _ hY
  have hscale : (2*Real.pi^2)^k*(tightScale ((n:ℝ)/(g:ℝ)))^(2*k)=(4*r Y)^k := by
    have hs := tightParameterScale_square Y hY
    have hs' : (2*Real.pi^2)*tightScale ((n:ℝ)/(g:ℝ))^2=4*r Y := by
      change (2*Real.pi^2)*tightParameterScale Y^2=4*r Y
      have hp : (2*Real.pi^2:ℝ)≠0 := by positivity
      field_simp at hs
      nlinarith
    rw [pow_mul,←mul_pow,hs']
  have hb : ∀i : Fin k,0<boundaryFactor 0 (x i) := by
    intro i
    exact lt_of_lt_of_le zero_lt_one (one_le_boundaryFactor 0 (x i))
  have hbprod : (∏i,boundaryFactor 0 (x i))≠0 := prod_ne_zero_iff.mpr (fun i _=>(hb i).ne')
  have hprod : (∏j : Fin (2*k),boundaryFactor 0 (connected_cut_boundaryVector k D hc c x j))=
      (∏i,boundaryFactor 0 (x i))^2 := by
    rw [connected_cut_boundaryVector_product k D hc c x,Finset.prod_pow]
  simp only [Critical.surviving_loop_intensity_eq_boundaryFactor,prod_mul_distrib,
    prod_const,card_univ,Fintype.card_fin,Finset.prod_pow]
  unfold connectedCutScaledCoefficientDensity connectedDensityCoefficientRatio
  rw [hscale,hprod]
  change _ = _ / (_*((4*r Y)^k*(∏i,boundaryFactor 0 (x i))^2)) * _
  generalize hA : realCoeff (TightMoments.momentTightG P (g-k) (2*k)
    (fun j=>connected_cut_boundaryVector k D hc c x j/tightScale ((n:ℝ)/(g:ℝ)))) n=A
  simp only [div_pow,one_pow]
  by_cases hv : realCoeff (Phi P g) n=0
  · simp [hv]
  · field_simp [hv,ha.ne',hr.ne',hbprod]



end WP.TightConnected
