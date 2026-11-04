import WPFormalization.Tight.SeparatingCoefficientRates
import WPFormalization.Tight.SeparatingOrbitValues
import WPFormalization.Tight.SeparatingPhysicalKernel

/- Actual cut kernels divided by the original geometric volume, obtained from the canonical coefficient transfer and the original dependent boundary enumeration. -/


noncomputable section
universe u v w z
namespace WP.TightSeparating
open Set Filter Finset MeasureTheory External TightMoments
open scoped Topology BigOperators ENNReal

lemma cutProductG_ofReal (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) xCritical) :
    (cutProductG P gs ps L (x : ℂ)).re =
      ∏ i, tightShiftedPolynomial P (gs i) (ps i) (inverseY x) (L i) := by
  unfold cutProductG
  simp_rw [momentTightG_ofReal P _ _ _ x hx]
  have he := map_prod Complex.ofRealHom
    (fun i => tightShiftedPolynomial P (gs i) (ps i) (inverseY x) (L i)) Finset.univ
  change (∏ i, Complex.ofRealHom (tightShiftedPolynomial P (gs i) (ps i) (inverseY x) (L i))).re = _
  rw [←he]
  rfl

lemma separating_kernel_ratio_of_coefficient_transfer {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {T : TightRegions G}
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Qgeom : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
    (BZ : BuddZonneveldTransform G T) (g k n : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) xCritical) (K C : ℝ) (hK : 0 ≤ K)
    (htransfer : ∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
      (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
      (∑ i, complexity (gs i) (ps i)) = complexity g 0 →
      ∀ L : (i : Fin Q) → Fin (ps i) → ℝ,
      realCoeff (cutProductG P gs ps L) n/realCoeff (Phi P g) n ≤
        K*((cutProductG P gs ps L (s : ℂ)).re/markedF P g 0 s))
    (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hvalue : (∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components),
        ∏ c, tightShiftedPolynomial P ((A.cut o).genus c) ((A.cut o).boundaryCount c)
          (inverseY s) ((A.cut o).tightProtectedLengths (fun i => Fin.elim0 i) x c)) /
        markedF P g 0 s ≤ C*(r (inverseY s))^k/(g : ℝ)) :
    (∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter (fun o => 2 ≤ (A.cut o).components),
      (A.cut o).tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x) /
      cuspVolume G g n ≤ K*C*(r (inverseY s))^k/((2*Real.pi^2)^k*(g : ℝ)) := by
  classical
  have hP : 0 < (2*Real.pi^2)^k := by positivity
  rw [Finset.sum_div]
  calc
    _ ≤ ∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter (fun o => 2 ≤ (A.cut o).components),
        (K*((cutProductG P (A.cut o).genus (A.cut o).boundaryCount
          ((A.cut o).tightProtectedLengths (fun i => Fin.elim0 i) x) (s : ℂ)).re/
            markedF P g 0 s))/(2*Real.pi^2)^k := by
      apply sum_le_sum
      intro o ho
      rw [tight_cut_kernel_volume_ratio T BZ g k n (A.cut o) hk hg
        (A.cut_connected o) (A.cut_stable o) (A.cut_euler o) x hx]
      apply div_le_div_of_nonneg_right _ hP.le
      have hb := Orbit.actual_cut_budgets A hk o
      exact htransfer _ _ _ hb.1 (A.cut_stable o) hb.2.2.1 _
    _ = (K/(2*Real.pi^2)^k)*((∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components),
        ∏ c, tightShiftedPolynomial P ((A.cut o).genus c) ((A.cut o).boundaryCount c)
          (inverseY s) ((A.cut o).tightProtectedLengths (fun i => Fin.elim0 i) x c)) /
        markedF P g 0 s) := by
      simp_rw [cutProductG_ofReal P _ _ _ s ⟨hs.1.le,hs.2⟩]
      rw [←Finset.sum_div,←Finset.mul_sum,←Finset.sum_div]
      ring
    _ ≤ (K/(2*Real.pi^2)^k)*(C*(r (inverseY s))^k/(g : ℝ)) :=
      mul_le_mul_of_nonneg_left hvalue (div_nonneg hK hP.le)
    _ = _ := by ring

end WP.TightSeparating
