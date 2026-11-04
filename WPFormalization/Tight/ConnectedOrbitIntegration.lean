import WPFormalization.Tight.ConnectedOrbitIntegrals
import WPFormalization.Tight.ConnectedOrbitMeasure
import WPFormalization.Tight.SpectrumTupleExtensionsTransport
import WPFormalization.Tight.SeparatingIntegralEnvelope

noncomputable section
namespace WP.TightConnected
open Set Filter Finset MeasureTheory External
open scoped Topology BigOperators ENNReal Pointwise

def connectedPhysicalCoefficientDensity (P : PsiTheory) (k g n : ℕ)
    (D : MulticurveCutData 0 k) (hc : D.components=1) (c : Fin D.components)
    (x : Fin k→ℝ) : ℝ :=
  (realCoeff (TightMoments.momentTightG P (g-k) (2*k)
    (connected_cut_boundaryVector k D hc c x)) n/realCoeff (Phi P g) n)/(2*Real.pi^2)^k*∏i,x i

lemma connected_physical_coefficient_density_continuous (P : PsiTheory) (k g n : ℕ)
    (D : MulticurveCutData 0 k) (hc : D.components=1) (c : Fin D.components) :
    Continuous (connectedPhysicalCoefficientDensity P k g n D hc c) := by
  unfold connectedPhysicalCoefficientDensity
  exact (((momentTightG_realCoeff_continuous P (g-k) (2*k) n).comp
    (connected_cut_boundaryVector_continuous k D hc c)).div_const _).div_const _ |>.mul (by fun_prop)

lemma connected_physical_scaled_integral (P : PsiTheory) (k g n : ℕ)
    (D : MulticurveCutData 0 k) (hc : D.components=1) (c : Fin D.components)
    (I : Fin k→Set ℝ) :
    (1/(2:ℝ)^k)*(∫x : Fin k→ℝ in {x|∀i,tightScale ((n:ℝ)/(g:ℝ))*x i∈I i},
      connectedPhysicalCoefficientDensity P k g n D hc c x) =
    ∫x : Fin k→ℝ in {x|∀i,x i∈I i},connectedCutScaledCoefficientDensity P k g n D hc c x := by
  have hα : 0<tightScale ((n:ℝ)/(g:ℝ)) := tightScale_pos _ (by positivity)
  rw [connected_window_dilation k _ hα I,←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  unfold connectedPhysicalCoefficientDensity connectedCutScaledCoefficientDensity
  dsimp only
  rw [connected_cut_boundaryVector_div]
  simp only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hpow : tightScale ((n:ℝ)/(g:ℝ))^(2*k)=
      tightScale ((n:ℝ)/(g:ℝ))^k*tightScale ((n:ℝ)/(g:ℝ))^k := by
    rw [←pow_add]
    congr 1
    omega
  rw [hpow]
  ring


lemma connected_cusp_volume_positive_eventually (P : PsiTheory)
    (G : WeilPeterssonGeometry P) :
    ∃N:ℕ,∀g≥N,∀n:ℕ,0<cuspVolume G g n := by
  obtain ⟨N,hN⟩ := connected_unmarked_positive_eventually P
  refine ⟨N+2,?_⟩
  intro g hg n
  rw [Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)]
  by_cases hn : n=0
  · subst n
    have hf : 0<realCoeff (Phi P g) 0 := by
      simpa [realCoeff,WP.coeff,markedF] using
        hN g (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩
    have he : volumeModel P g 0 = ((2*Real.pi^2)^(dimension g 0))*
        realCoeff (Phi P g) 0 := by
      rw [TightSeparating.unmarked_realCoeff_volume]
      simp only [Nat.factorial_zero,Nat.cast_one,mul_one]
      field_simp
    rw [he]
    positivity
  · exact diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)

lemma connected_orbit_scaled_window_expectation_eq {P : PsiTheory}
    {G : WeilPeterssonGeometry P} (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    {H : HyperbolicCurveGeometry G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (g k n : ℕ) (hg : 2≤g) (o : A.Orbit g 0 k) (ho : (A.cut o).components=1)
    (c : Fin (A.cut o).components) (hv : 0<cuspVolume G g n)
    (I : Fin k→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (_hB : 0≤B) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    (∫⁻X, A.orbitSum o
      ({x : Fin k→ℝ|∀i,tightScale ((n:ℝ)/(g:ℝ))*x i∈I i}.indicator (fun _=>1)) X
      ∂((G.wpMeasure g n (fun _=>0) univ)⁻¹ •
        G.wpMeasure g (0+n) (Fin.append (fun _ : Fin 0=>0) (fun _ : Fin n=>0)))) =
    ENNReal.ofReal (∫x : Fin k→ℝ in {x|∀i,x i∈I i},
      connectedCutScaledCoefficientDensity P k g n (A.cut o) ho c x) := by
  classical
  let α := tightScale ((n:ℝ)/(g:ℝ))
  let J : Fin k→Set ℝ := fun i=>{t|α*t∈I i}
  let W : Set (Fin k→ℝ) := {x|∀i,x i∈J i}
  let V : (Fin k→ℝ)→ℝ := fun x=>(A.cut o).tightCutKernel T
    (fun _ : Fin 0=>0) (fun _ : Fin n=>0) x
  let F := connectedPhysicalCoefficientDensity P k g n (A.cut o) ho c
  have hα : 0<α := tightScale_pos _ (by positivity)
  have hJ : ∀i,MeasurableSet (J i) := fun i=>(measurable_const.mul measurable_id) (hI i)
  have hW : MeasurableSet W := RandomGeometry.pants_numeric_window_set_measurable k J hJ
  have hJB : ∀i,J i⊆Icc (0:ℝ) (B/α) := by
    intro i t ht
    have h := hIB i ht
    exact ⟨by nlinarith [h.1],(le_div_iff₀ hα).mpr (by simpa only [mul_comm] using h.2)⟩
  have hW0 : W⊆{x : Fin k→ℝ|∀i,0≤x i} := fun x hx i=>(hJB i (hx i)).1
  have hrestrict : volume.restrict W =
      (volume.restrict {x : Fin k→ℝ|∀i,0≤x i}).restrict W := by
    rw [Measure.restrict_restrict hW,inter_eq_left.mpr hW0]
  have hFinteg : Integrable F (volume.restrict W) :=
    RandomGeometry.pants_window_integrable_continuous k J (B/α) hJB F
      (connected_physical_coefficient_density_continuous P k g n (A.cut o) ho c)
  have hempty : (fun i : Fin 0=>Fin.elim0 i)=(fun _=> (0:ℝ)) := funext (fun i=>Fin.elim0 i)
  have hVpos (x : Fin k→ℝ) : 0≤V x := by
    simpa only [V,←hempty] using TightSeparating.tight_cut_kernel_nonneg T (A.cut o) x
  have hFeq (x : Fin k→ℝ) (hx : ∀i,0≤x i) :
      F x=V x/cuspVolume G g n*∏i,x i := by
    unfold F connectedPhysicalCoefficientDensity
    rw [←connected_cut_kernel_volume_ratio T BZ g k n (A.cut o) ho hg
      (A.cut_stable o) (A.cut_euler o) c x hx,hempty]
  have hFnonneg : 0≤ᵐ[volume.restrict W] F := by
    filter_upwards [ae_restrict_mem hW] with x hx
    rw [hFeq x (hW0 hx)]
    exact mul_nonneg (div_nonneg (hVpos x) hv.le) (prod_nonneg (fun i _=>hW0 hx i))
  have hm : G.wpMeasure g n (fun _=>0) univ=ENNReal.ofReal (cuspVolume G g n) := by
    exact (ENNReal.ofReal_toReal (G.finite_volume g n _ (by unfold Stable;omega) (by simp))).symm
  have hind : (fun x : Fin k→ℝ=>W.indicator (fun _=> (1:ℝ≥0∞)) x*
      ENNReal.ofReal (V x)*∏i,ENNReal.ofReal (x i)) =
      W.indicator (fun x=>ENNReal.ofReal (V x)*∏i,ENNReal.ofReal (x i)) := by
    funext x
    by_cases hx : x∈W <;> simp [hx]
  have hregion : T.region g 0 n (fun _=>0) (fun _=>0)=univ := by
    ext X
    simp [TightRegions.region,tightLocus]
  have hMI : (∫⁻X,A.orbitSum o (W.indicator (fun _=>1)) X
      ∂G.wpMeasure g (0+n) (Fin.append (fun _ : Fin 0=>0) (fun _ : Fin n=>0))) =
      ((2:ℝ≥0∞)^k)⁻¹*∫⁻x : Fin k→ℝ in W,ENNReal.ofReal (V x)*∏i,ENNReal.ofReal (x i) := by
    calc
      _ = ∫⁻X in T.region g 0 n (fun _=>0) (fun _=>0),
        A.orbitSum o (W.indicator (fun _=>1)) X
          ∂G.wpMeasure g (0+n) (Fin.append (fun _ : Fin 0=>0) (fun _ : Fin n=>0)) := by
            rw [hregion,Measure.restrict_univ]
      _ = _ := by
        rw [MI.orbit_integral o (by unfold Stable;omega) _ _ (fun i=>Fin.elim0 i)
          (fun _=>le_rfl) _ (measurable_const.indicator hW),MI.coefficient_connected o ho]
        rw [hind,lintegral_indicator hW,←hrestrict]
  have hnorm : (G.wpMeasure g n (fun _=>0) univ)⁻¹ *
      (∫⁻x : Fin k→ℝ in W,ENNReal.ofReal (V x)*∏i,ENNReal.ofReal (x i)) =
        ENNReal.ofReal (∫x in W,F x) := by
    rw [hm,←lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by positivity)),
      ofReal_integral_eq_lintegral_ofReal hFinteg hFnonneg]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hW] with x hx
    rw [hFeq x (hW0 hx),ENNReal.ofReal_mul (div_nonneg (hVpos x) hv.le),
      ENNReal.ofReal_div_of_pos hv,
      ENNReal.ofReal_prod_of_nonneg (fun i _=>hW0 hx i)]
    simp only [div_eq_mul_inv]
    ring
  rw [lintegral_smul_measure]
  simp only [smul_eq_mul]
  change (G.wpMeasure g n (fun _=>0) univ)⁻¹ *
    (∫⁻X,A.orbitSum o (W.indicator (fun _=>1)) X
      ∂G.wpMeasure g (0+n) (Fin.append (fun _ : Fin 0=>0) (fun _ : Fin n=>0))) = _
  rw [hMI]
  rw [mul_left_comm _ _ (∫⁻x : Fin k→ℝ in W,ENNReal.ofReal (V x)*∏i,ENNReal.ofReal (x i)),hnorm]
  rw [←connected_physical_scaled_integral P k g n (A.cut o) ho c I,
    ENNReal.ofReal_mul (by positivity : 0≤1/(2:ℝ)^k),ENNReal.ofReal_div_of_pos (by positivity)]
  simp [W,J,α,F,ENNReal.ofReal_pow]

end WP.TightConnected
