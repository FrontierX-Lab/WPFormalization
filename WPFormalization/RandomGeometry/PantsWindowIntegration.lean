import WPFormalization.RandomGeometry.PantsWindowCount
import WPFormalization.RandomGeometry.PantsWindowIntegralDefinitions
import WPFormalization.RandomGeometry.PantsMoments

/-! Equation (14.6) for arbitrary measurable short physical-length windows.
The left side is the literal integer count of ordered distinct actual geodesics;
the right side retains the exact cusp-label coefficient and physical Jacobian. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n r m : ℕ}

lemma pants_window_orthant_lintegral (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hpos : ∀i x, x ∈ I i → 0 ≤ x) :
    (∫⁻ x : Fin r → ℝ in {x | ∀i, 0 ≤ x i},
      pantsWindowTest I x * ENNReal.ofReal
        (boundaryVolumeModel P g m (activeBoundaryLengths hr x)) * ∏i, ENNReal.ofReal (x i)) =
      ∫⁻ x : Fin r → ℝ in {x | ∀i, x i ∈ I i},
        ENNReal.ofReal (boundaryVolumeModel P g m (activeBoundaryLengths hr x))*
          ∏i, ENNReal.ofReal (x i) := by
  classical
  let B : Set (Fin r → ℝ) := {x | ∀i, x i ∈ I i}
  let f := fun x : Fin r → ℝ => ENNReal.ofReal
    (boundaryVolumeModel P g m (activeBoundaryLengths hr x))*∏i, ENNReal.ofReal (x i)
  have hfun : (fun x => pantsWindowTest I x*f x)=B.indicator f := by
    funext x
    by_cases hx : ∀i, x i ∈ I i <;> simp [pantsWindowTest,Set.indicator,B,hx]
  have hB : MeasurableSet B := pants_window_set_measurable I hI
  have hinter : B ∩ {x | ∀i, 0 ≤ x i}=B := by
    apply Set.inter_eq_left.mpr
    intro x hx i
    exact hpos i (x i) (hx i)
  change (∫⁻ x in {x | ∀i, 0 ≤ x i}, (pantsWindowTest I x*
    ENNReal.ofReal (boundaryVolumeModel P g m (activeBoundaryLengths hr x)))*
      ∏i, ENNReal.ofReal (x i))=_
  simp only [mul_assoc]
  change (∫⁻ x in {x | ∀i, 0 ≤ x i}, pantsWindowTest I x*f x)=_
  rw [hfun,lintegral_indicator hB,Measure.restrict_restrict hB,hinter]

lemma pants_window_lintegral_toReal (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (g m r : ℕ) (hr : r ≤ m)
    (hst : Stable g m) (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hpos : ∀i x, x ∈ I i → 0 ≤ x) :
    (∫⁻ x : Fin r → ℝ in {x | ∀i, 0 ≤ x i},
      pantsWindowTest I x * ENNReal.ofReal
        (boundaryVolumeModel P g m (activeBoundaryLengths hr x)) * ∏i, ENNReal.ofReal (x i)).toReal =
      pantsWindowVolumeIntegral P g m r hr I := by
  rw [pants_window_orthant_lintegral P g m r hr I hI hpos]
  have hm : Continuous (fun x : Fin r → ℝ =>
      boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏i, x i) := by
    have hb : Continuous (boundaryVolumeModel P g m) := by unfold boundaryVolumeModel; fun_prop
    exact (hb.comp (activeBoundaryLengths_continuous hr)).mul (by fun_prop)
  have hnonneg : 0 ≤ᵐ[volume.restrict {x : Fin r → ℝ | ∀i, x i ∈ I i}]
      (fun x => boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏i, x i) := by
    filter_upwards [ae_restrict_mem (pants_window_set_measurable I hI)] with x hx
    have hx0 : ∀i, 0 ≤ x i := fun i => hpos i (x i) (hx i)
    have hv : 0 ≤ boundaryVolumeModel P g m (activeBoundaryLengths hr x) := by
      rw [←WP.Geometry.wpVolume_eq_boundaryVolumeModel P G g m _ hst
        (activeBoundaryLengths_nonneg hr x hx0)]
      exact ENNReal.toReal_nonneg
    exact mul_nonneg hv (Finset.prod_nonneg (fun i _ => hx0 i))
  rw [pantsWindowVolumeIntegral,integral_eq_lintegral_of_nonneg_ae hnonneg hm.aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (pants_window_set_measurable I hI)] with x hx
  have hx0 : ∀i, 0 ≤ x i := fun i => hpos i (x i) (hx i)
  have hw : 0 ≤ ∏i, x i := Finset.prod_nonneg (fun i _ => hx0 i)
  rw [mul_comm (boundaryVolumeModel P g m (activeBoundaryLengths hr x)),
    ENNReal.ofReal_mul hw,ENNReal.ofReal_prod_of_nonneg (fun i _ => hx0 i),mul_comm]

include C MI in
lemma pants_windows_moment_model (hg : 2 ≤ g) (hr : 0 < r) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) (hsub : ∀i, I i ⊆ Set.Icc 0 L) :
    (∫X : G.Moduli g n (fun _ => 0), (pantsWindowCount H X L I : ℝ) ∂wpProbability G g n) =
      ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*volumeModel P g n))*
        pantsWindowVolumeIntegral P g (n-r) r (show r ≤ n-r by omega) I := by
  have hm : Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (pantsWindowCount H X L I : ℝ)) :=
    pantsWindowCount_measurable H T C MI (by omega) hr L hL I hI hsub
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
    (fun X => Nat.cast_nonneg (pantsWindowCount H X L I))) hm.aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast]
  have hfun : (fun X : G.Moduli g n (fun _ => 0) => (pantsWindowCount H X L I : ℝ≥0∞)) =
      fun X => pantsWindowSum (H:=H) X L (pantsWindowTest I) := by
    funext X
    exact (pantsWindowSum_test_eq_count H X L I).symm
  rw [hfun,pants_window_probability_integral T C MI hg hr hn L hL _
    (pantsWindowTest_measurable I hI) (pantsWindowTest_support I L hsub)]
  have hmass : (G.wpMeasure g n (fun _ => 0) Set.univ).toReal=volumeModel P g n :=
    WP.Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    hmass,pants_window_lintegral_toReal P G g (n-r) r (show r ≤ n-r by omega)
      (by unfold Stable;omega) I hI (fun i x hx => (hsub i hx).1),
    pantsStarOrbit_card_real G H T g n r hg]
  ring

def pantsGeometricWindowIntegral (G : WeilPeterssonGeometry.{u,v} P)
    (g m r : ℕ) (hr : r ≤ m) (I : Fin r → Set ℝ) : ℝ :=
  ∫ x : Fin r → ℝ in {x | ∀i, x i ∈ I i},
    wpVolume G g m (activeBoundaryLengths hr x)*∏i, x i

lemma pantsGeometricWindowIntegral_eq_model (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (g m r : ℕ) (hr : r ≤ m)
    (hst : Stable g m) (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hpos : ∀i x, x ∈ I i → 0 ≤ x) :
    pantsGeometricWindowIntegral G g m r hr I=pantsWindowVolumeIntegral P g m r hr I := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (pants_window_set_measurable I hI)] with x hx
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G g m _ hst
    (activeBoundaryLengths_nonneg hr x (fun i => hpos i (x i) (hx i)))]

include C MI in
lemma pants_windows_moment (hg : 2 ≤ g) (hr : 0 < r) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) (hsub : ∀i, I i ⊆ Set.Icc 0 L) :
    (∫X : G.Moduli g n (fun _ => 0), (pantsWindowCount H X L I : ℝ) ∂wpProbability G g n) =
      ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*cuspVolume G g n))*
        pantsGeometricWindowIntegral G g (n-r) r (show r ≤ n-r by omega) I := by
  rw [WP.Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega),
    pantsGeometricWindowIntegral_eq_model P G g (n-r) r (show r ≤ n-r by omega)
      (by unfold Stable;omega) I hI (fun i x hx => (hsub i hx).1)]
  exact pants_windows_moment_model G H T C MI hg hr hn L hL I hI hsub

end WP.RandomGeometry
