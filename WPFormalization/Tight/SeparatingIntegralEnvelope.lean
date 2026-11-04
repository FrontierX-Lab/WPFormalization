import WPFormalization.Tight.SeparatingPhysicalKernel
import WPFormalization.Critical.CutBoxIntegral

noncomputable section
universe u v w z
namespace WP.TightSeparating
open Set Filter Finset MeasureTheory External
open scoped Topology BigOperators ENNReal

lemma tight_cut_kernel_nonneg {P : PsiTheory} {G : WeilPeterssonGeometry P}
    (T : TightRegions G) {k n : ℕ} (D : MulticurveCutData 0 k) (x : Fin k → ℝ) :
    0 ≤ D.tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x := by
  unfold MulticurveCutData.tightCutKernel
  exact sum_nonneg (fun a _ => prod_nonneg (fun c _ => ENNReal.toReal_nonneg))

/-- Sum the exact classical orbit integrations before applying the physical
box envelope. The topological coefficients are bounded by one, as in F.3. -/
lemma separating_orbit_integral_envelope {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (I : BuddLionsTightIntegration G T H Q A)
    (g k n : ℕ) (hg : 2 ≤ g) (s : Finset (A.Orbit g 0 k))
    (ell U : ℝ) (hell : 0 ≤ ell) (hU : 0 ≤ U)
    (hbound : ∀ x ∈ Critical.cutLengthBox k ell,
      (∑ o ∈ s, (A.cut o).tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x) ≤ U) :
    (∑ o ∈ s, ∫⁻ X in T.region g 0 n (fun i => Fin.elim0 i) (fun _ => 0),
      A.orbitSum o (Critical.cutLengthTest k ell) X
        ∂G.wpMeasure g (0+n) (Fin.append (fun i => Fin.elim0 i) (fun _ => 0))) ≤
      ENNReal.ofReal (U*ell^(2*k)) := by
  classical
  let V : A.Orbit g 0 k → (Fin k → ℝ) → ℝ := fun o x =>
    (A.cut o).tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x
  let f : A.Orbit g 0 k → (Fin k → ℝ) → ℝ≥0∞ := fun o x =>
    Critical.cutLengthTest k ell x*ENNReal.ofReal (V o x)*∏ e, ENNReal.ofReal (x e)
  have hfm (o : A.Orbit g 0 k) : Measurable (f o) := by
    apply Measurable.mul
    · exact (Critical.cutLengthTest_measurable k ell).mul
        (I.cutKernel_measurable o (fun i => Fin.elim0 i) (fun _ : Fin n => 0)).ennreal_ofReal
    · exact Finset.measurable_prod _ (fun e _ => (measurable_pi_apply e).ennreal_ofReal)
  calc
    _ = ∑ o ∈ s, I.coefficient o *
        ∫⁻ x : Fin k → ℝ in {x | ∀ e, 0 ≤ x e}, f o x := by
      apply sum_congr rfl
      intro o ho
      exact I.orbit_integral o (by unfold Stable;omega) _ _
        (fun i => Fin.elim0 i) (fun _ => le_rfl) _ (Critical.cutLengthTest_measurable k ell)
    _ ≤ ∑ o ∈ s, ∫⁻ x : Fin k → ℝ in {x | ∀ e, 0 ≤ x e}, f o x := by
      apply sum_le_sum
      intro o ho
      exact (mul_le_mul' (I.coefficient_le_one o) le_rfl).trans_eq (one_mul _)
    _ = ∫⁻ x : Fin k → ℝ in {x | ∀ e, 0 ≤ x e}, ∑ o ∈ s, f o x :=
      (lintegral_finsetSum s (fun o _ => hfm o)).symm
    _ = ∫⁻ x : Fin k → ℝ in {x | ∀ e, 0 ≤ x e},
        Critical.cutLengthTest k ell x*ENNReal.ofReal (∑ o ∈ s, V o x)*
          ∏ e, ENNReal.ofReal (x e) := by
      apply lintegral_congr
      intro x
      dsimp only [f]
      rw [ENNReal.ofReal_sum_of_nonneg (fun o _ => tight_cut_kernel_nonneg T (A.cut o) x),
        Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := Critical.cut_box_integral_envelope k ell U hell hU _ hbound

end WP.TightSeparating
