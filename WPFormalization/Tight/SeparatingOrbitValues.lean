import WPFormalization.Tight.SeparatingOrbitSum
import WPFormalization.Tight.SeparatingBoundaryValues
import WPFormalization.Tight.ConnectedPoissonPhi

noncomputable section
universe u v w z
namespace WP.TightSeparating
open Set Finset External
open scoped BigOperators

/-- The actual separating orbit sum of tight values on a fixed scaled box.
No permutation of a dependent boundary enumeration is needed: the all-stable
boundary estimate is applied to each original orbit before skeleton grouping. -/
lemma separating_orbit_tight_value_sum {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
    {Qgeom : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
    (k : ℕ) (hk : 1 ≤ k) (L0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ g ≥ N, ∀ Y ∈ Ico (0 : ℝ) y₀,
      ∀ x : Fin k → ℝ,
      (∀ e, 0 ≤ tightParameterScale Y*x e ∧ tightParameterScale Y*x e ≤ L0) →
      (∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter (fun o => 2 ≤ (A.cut o).components),
        ∏ c, tightShiftedPolynomial P ((A.cut o).genus c) ((A.cut o).boundaryCount c) Y
          ((A.cut o).tightProtectedLengths (fun i => Fin.elim0 i) x c)) /
        markedF P g 0 (XR Y) ≤ C*(r Y)^k/(g : ℝ) := by
  classical
  obtain ⟨C,hC,N,hbound⟩ := separating_orbit_amplitude_sum A k hk
  obtain ⟨B,hB,hboundary⟩ := tight_boundary_value_upper P L0
  obtain ⟨G0,hF0⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨B^(2*k)*C,by positivity,max N G0,?_⟩
  intro g hg Y hY x hx
  have hX : XR Y ∈ Ico (0 : ℝ) xCritical :=
    ⟨XR_nonneg_interior Y hY,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have hF := hF0 g (le_of_max_le_right hg) _ hX
  have hterm (o : A.Orbit g 0 k) :
      (∏ c, tightShiftedPolynomial P ((A.cut o).genus c) ((A.cut o).boundaryCount c) Y
        ((A.cut o).tightProtectedLengths (fun i => Fin.elim0 i) x c)) ≤
      B^(2*k)*(∏ c, markedF P ((A.cut o).genus c) ((A.cut o).boundaryCount c) (XR Y)) := by
    have hb := Orbit.actual_cut_budgets A hk o
    calc
      _ ≤ ∏ c, B^((A.cut o).boundaryCount c)*
          markedF P ((A.cut o).genus c) ((A.cut o).boundaryCount c) (XR Y) :=
        Finset.prod_le_prod₀ (fun c _ => (tightShiftedPolynomial_pos P _ _ (hb.1 c)
          (A.cut_stable o c) Y hY _).le)
          (fun c _ => hboundary _ _ (hb.1 c) (A.cut_stable o c) Y hY _
            (empty_cut_lengths_box (A.cut o) _ L0 x hx c))
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hb.2.1]
  have hsum := sum_le_sum (s := (univ : Finset (A.Orbit g 0 k)).filter
    (fun o => 2 ≤ (A.cut o).components)) (fun o _ => hterm o)
  rw [←mul_sum] at hsum
  calc
    _ ≤ (B^(2*k)*(∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components),
        ∏ c, markedF P ((A.cut o).genus c) ((A.cut o).boundaryCount c) (XR Y)))/
        markedF P g 0 (XR Y) := div_le_div_of_nonneg_right hsum hF.le
    _ = B^(2*k)*((∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components),
        ∏ c, markedF P ((A.cut o).genus c) ((A.cut o).boundaryCount c) (XR Y))/
        markedF P g 0 (XR Y)) := by ring
    _ ≤ B^(2*k)*(C*(r Y)^k/(g : ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound g (le_of_max_le_left hg) Y hY) (by positivity)
    _ = _ := by ring

end WP.TightSeparating
