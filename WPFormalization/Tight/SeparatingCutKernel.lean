import WPFormalization.Tight.SeparatingPositiveProduct
import WPFormalization.Tight.CuspSpecialization
import WPFormalization.Critical.CutCuspLabels
import WPFormalization.Critical.CutGraphData
import WPFormalization.External.BuddLionsTightIntegration

noncomputable section
namespace WP.TightSeparating
open Set Filter Finset PositiveConvolution External
open scoped Topology BigOperators

lemma realTaylor_finite_product {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (hp : ∀ i ∈ s, PositiveJets (f i)) :
    Analysis.realTaylor (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, Analysis.realTaylor (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    apply Analysis.realTaylor_of_taylor_map
    simp
  | @insert i s hi ih =>
    have hfs : ∀ j ∈ s, AnalyticAt ℂ (f j) 0 := fun j hj => hf j (mem_insert_of_mem hj)
    have hps : ∀ j ∈ s, PositiveJets (f j) := fun j hj => hp j (mem_insert_of_mem hj)
    have htail := PositiveJets.prod s f hfs hps
    simp only [Finset.prod_insert hi]
    rw [Analysis.realTaylor_mul (hf i (mem_insert_self _ _))
      (Finset.analyticAt_fun_prod _ hfs)
      (fun n => ((hp i (mem_insert_self _ _)).coefficient_nonneg n).2)
      (fun n => (htail.coefficient_nonneg n).2),ih hfs hps]

lemma momentTightG_positiveJets (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (L : Fin p → ℝ) : PositiveJets (TightMoments.momentTightG P g p L) := by
  have h := cutProductG_positiveJets P (fun _ : Fin 1 => g) (fun _ : Fin 1 => p)
    (fun _ => hp) (fun _ => hs) (fun _ => L)
  change PositiveJets (fun z => ∏ _i : Fin 1, TightMoments.momentTightG P g p L z) at h
  simpa only [Fin.prod_univ_one] using h

lemma cutProductG_realTaylor (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) :
    Analysis.realTaylor (cutProductG P gs ps L) =
      ∏ i, Analysis.realTaylor (TightMoments.momentTightG P (gs i) (ps i) (L i)) := by
  have hz : ‖(0 : ℂ)‖ < xCritical := by simpa using Analysis.xCritical_pos_parameter
  exact realTaylor_finite_product _ _
    (fun i _ => TightMoments.momentTightG_analyticAt P (gs i) (ps i) (L i) 0 hz)
    (fun i _ => momentTightG_positiveJets P _ _ (hp i) (hs i) _)

/-- Exact labeled-cusp coefficient extraction for an actual fixed cut family.
Each free cusp is assigned once; the local factorials produce exactly n!. -/
lemma cut_product_labeled_coefficients (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (n : ℕ) :
    (∑ a : Fin n → Fin Q,
      ∏ i, ((Critical.cutCuspHistogram a i).factorial : ℝ)*
        realCoeff (TightMoments.momentTightG P (gs i) (ps i) (L i))
          (Critical.cutCuspHistogram a i)) =
      (n.factorial : ℝ)*realCoeff (cutProductG P gs ps L) n := by
  have h := Critical.cutCuspLabels_series_coeff n Q
    (fun i => Analysis.realTaylor (TightMoments.momentTightG P (gs i) (ps i) (L i)))
  rw [←cutProductG_realTaylor P gs ps hp hs L] at h
  simpa only [Analysis.realTaylor_coeff] using h

end WP.TightSeparating
namespace WP.TightSeparating
open Set Filter Finset PositiveConvolution External
open scoped Topology BigOperators

/-- The exact label-assignment sum for actual geometric tight volumes. -/
lemma cut_volume_labeled_coefficient {P : PsiTheory} {G : WeilPeterssonGeometry P}
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    {Q : ℕ} (gs ps : Fin Q → ℕ) (hp : ∀ i, 1 ≤ ps i)
    (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (hL : ∀ i j, 0 ≤ L i j) (n : ℕ) :
    (∑ a : Fin n → Fin Q, ∏ i,
      tightVolume T (gs i) (ps i) (Critical.cutCuspHistogram a i) (L i) (fun _ => 0)) =
      (2*Real.pi^2)^((∑ i, dimension (gs i) (ps i))+n) *
        (n.factorial : ℝ)*realCoeff (cutProductG P gs ps L) n := by
  let P0 : ℝ := 2*Real.pi^2
  have hP0 : P0 ≠ 0 := by dsimp [P0];positivity
  have hloc (a : Fin n → Fin Q) (i : Fin Q) :
      tightVolume T (gs i) (ps i) (Critical.cutCuspHistogram a i) (L i) (fun _ => 0) =
        P0^(dimension (gs i) (ps i)+Critical.cutCuspHistogram a i)*
          (((Critical.cutCuspHistogram a i).factorial : ℝ)*
            realCoeff (TightMoments.momentTightG P (gs i) (ps i) (L i))
              (Critical.cutCuspHistogram a i)) := by
    have h := TightMoments.geometric_tight_cusp_coefficient T BZ (gs i) (ps i) (hs i)
      (L i) (hL i) (Critical.cutCuspHistogram a i)
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero _ hP0) (by positivity))).mp at h
    convert h using 1 <;> ring
  have hterm (a : Fin n → Fin Q) :
      (∏ i, tightVolume T (gs i) (ps i) (Critical.cutCuspHistogram a i) (L i) (fun _ => 0)) =
        P0^((∑ i, dimension (gs i) (ps i))+n)*
          (∏ i, ((Critical.cutCuspHistogram a i).factorial : ℝ)*
            realCoeff (TightMoments.momentTightG P (gs i) (ps i) (L i))
              (Critical.cutCuspHistogram a i)) := by
    simp_rw [hloc]
    rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
      Finset.sum_add_distrib,Critical.cutCuspHistogram_sum]
  simp_rw [hterm]
  rw [←mul_sum,cut_product_labeled_coefficients P gs ps hp hs L n]
  dsimp [P0]
  ring

lemma tight_cut_dimension_budget (g k : ℕ) (D : MulticurveCutData 0 k)
    (hs : ∀ i, Stable (D.genus i) (D.boundaryCount i))
    (heuler : (∑ i, D.genus i)+k+1=g+D.components) (hg : 2 ≤ g) :
    (∑ i, dimension (D.genus i) (D.boundaryCount i))+k=dimension g 0 := by
  have he (i : Fin D.components) :
      dimension (D.genus i) (D.boundaryCount i)+3=3*D.genus i+D.boundaryCount i := by
    have hi := hs i
    unfold Stable at hi
    unfold dimension
    omega
  have hh := congrArg (fun f : Fin D.components → ℕ => ∑ i, f i) (funext he)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,←Finset.mul_sum] at hh
  rw [D.sum_boundaryCount] at hh
  change (∑ i, dimension (D.genus i) (D.boundaryCount i))+k=3*g-3
  omega

/-- Exact physical cut-kernel coefficient, including the P^(-k) cost.
The n free boundary labels in the classical formula are never collapsed early. -/
lemma tight_cut_kernel_coefficient {P : PsiTheory} {G : WeilPeterssonGeometry P}
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (g k n : ℕ) (D : MulticurveCutData 0 k)
    (hk : 1 ≤ k) (hg : 2 ≤ g) (hconn : D.ConnectedWithin univ)
    (hs : ∀ i, Stable (D.genus i) (D.boundaryCount i))
    (heuler : (∑ i, D.genus i)+k+1=g+D.components)
    (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i) :
    D.tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x /
        ((2*Real.pi^2)^(dimension g 0+n)*(n.factorial : ℝ)) =
      realCoeff (cutProductG P D.genus D.boundaryCount
        (D.tightProtectedLengths (fun i => Fin.elim0 i) x)) n / (2*Real.pi^2)^k := by
  have hp := Critical.CutGraphData.boundaryCount_pos D hk hconn
  have hL : ∀ i j, 0 ≤ D.tightProtectedLengths (fun i => Fin.elim0 i) x i j := by
    intro i j
    unfold MulticurveCutData.tightProtectedLengths
    split
    · rename_i q he
      exact Fin.elim0 q.val
    · exact hx _
  have hcounts (a : Fin n → Fin D.components) (i : Fin D.components) :
      D.assignedCount a i = Critical.cutCuspHistogram a i :=
    (Critical.cutCuspHistogram_eq_card a i).symm
  have hkernel : D.tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x =
      (∑ a : Fin n → Fin D.components, ∏ i,
        tightVolume T (D.genus i) (D.boundaryCount i) (Critical.cutCuspHistogram a i)
          (D.tightProtectedLengths (fun i => Fin.elim0 i) x i) (fun _ => 0)) := by
    unfold MulticurveCutData.tightCutKernel
    apply sum_congr rfl
    intro a ha
    apply prod_congr rfl
    intro i hi
    change tightVolume T (D.genus i) (D.boundaryCount i) (D.assignedCount a i)
      (D.tightProtectedLengths (fun i => Fin.elim0 i) x i) (fun _ => 0) = _
    rw [hcounts]
  rw [hkernel,cut_volume_labeled_coefficient T BZ D.genus D.boundaryCount hp hs _ hL n]
  have hdim := tight_cut_dimension_budget g k D hs heuler hg
  have he : dimension g 0+n=k+((∑ i, dimension (D.genus i) (D.boundaryCount i))+n) := by omega
  rw [he,pow_add]
  have hP : (2*Real.pi^2 : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

end WP.TightSeparating
