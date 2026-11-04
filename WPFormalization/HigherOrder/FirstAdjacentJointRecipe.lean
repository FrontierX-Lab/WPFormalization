import WPFormalization.HigherOrder.LinearJointRecipes
import WPFormalization.HigherOrder.SeparatingSeriesJointRecipe
/-! The first-coordinate increment of the actual canonical algorithm has a joint finite-data polynomial from strictly lower profile/cusp/genus recipes. All three original operators, including the empty merger case, are supplied by proved actual producers. Degree is at most D+1. This is a current induction step; no all-order certificates are asserted. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set PowerSeries
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma actual_first_adjacent_joint_recipe (P : PsiTheory) (m K b B D : ℕ)
    (hBH : 2 * b + 2 ≤ B) (hBS : b + (3 * K) / 2 + 2 ≤ B)
    (F : ∀ q : ℕ, ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ q i, i < K → ∀ τ, (F q i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ q i, i < K → ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ v : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun k => (v k : ℝ)) (F q i (classify (q + 1) b v)))
    (A : R) (c g : ℕ → ℕ → R)
    (hA : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y) A = WP.A Y)
    (hc : ∀ q ≥ 1, ∀ i < K, ∀ Y ∈ Icc (0 : ℝ) y₀, cuspCoefficient P Y q i = (φ Y) (c q i))
    (hg : ∀ q ≥ 1, ∀ i < K, ∀ Y ∈ Icc (0 : ℝ) y₀, genusCoefficient P Y q i = (φ Y) (g q i))
    (κ : ThetaPolynomial ((3 * K) / 2 + 1) →+* R)
    (hκ : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y).comp κ =
      MvPolynomial.eval (fun i : Fin ((3 * K) / 2 + 2) => theta Y i.val))
    (M W : ℕ → R)
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D + 1 →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ l : ℕ, l < B + 1 → weight Y l = (φ Y) (W l)) :
    ∃ Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R,
      (∀ σ, (Q σ).totalDegree ≤ D + 1) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
        adjacentCoefficient P Y (formalHierarchyJet P Y) K 0 (List.ofFn d) =
          MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify (m + 1) B d)) := by
  have hmerge : ∃ Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R,
      (∀ σ, (Q σ).totalDegree ≤ D + 1) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
        PowerSeries.coeff K (mergerSeries Y (formalHierarchyJet P Y) (d 0) (List.ofFn (fun i => d i.succ))) =
          MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify (m + 1) B d)) := by
    cases m with
    | zero =>
      refine ⟨fun _ => 0, by intro σ; simp, ?_⟩
      intro Y hY d
      simp [mergerSeries, formalHierarchyJet]
    | succ q =>
      refine ⟨(fun σ => mergerSeriesJointRecipe q K b B σ (F q) A (c (q + 1)) M W), ?_, ?_⟩
      · intro σ
        exact mergerSeriesJointRecipe_degree q K b B D σ (F q) (hdegree q) A (c (q + 1)) M W
      · exact actual_merger_series_joint_recipe P q K b B D (by omega) (F q) (hdegree q) φ (hactual q)
          A (c (q + 1)) M W hA (hc (q + 1) (by omega))
          (by intro Y hY k hk; exact hm Y hY k (by omega))
          (by intro Y hY l hl; exact hw Y hY l (by omega))
  obtain ⟨QM, hQM, hM⟩ := hmerge
  let QH : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R := fun σ =>
    handleContributionRecipe K b B (pivotHeadCoefficients m) σ Fin.succ (F (m + 1)) A (c (m + 2)) (g (m + 1)) M W
  have hQH (σ) : (QH σ).totalDegree ≤ D + 1 :=
    handleContributionRecipe_degree K b B D _ σ _ _ (hdegree (m + 1)) _ _ _ _ _
  have hH : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
      PowerSeries.coeff K (nonseparatingSeries Y (formalHierarchyJet P Y) (d 0) (List.ofFn (fun i => d i.succ))) =
        MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (QH (classify (m + 1) B d)) := by
    simpa only [pivotHeadCoefficients_sum] using actual_nonseparating_contribution_recipe P (m + 1) m K b B D hBH
      (pivotHeadCoefficients m) Fin.succ (F (m + 1)) (hdegree (m + 1)) φ (hactual (m + 1))
      A (c (m + 2)) (g (m + 1)) M W hA (hc (m + 2) (by omega)) (hg (m + 1) (by omega)) hm
      (by intro Y hY l hl; exact hw Y hY l (by omega))
  obtain ⟨QS, hQS, hS⟩ := actual_separating_series_joint_recipe P m K b B D hBS F hdegree φ hactual
    A c g hA hc hg κ hκ M W (by intro Y hY k hk; exact hm Y hY k (by omega))
    (by intro Y hY l hl; exact hw Y hY l (by omega))
  let Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R :=
    fun σ => -(QM σ + QH σ + QS σ)
  refine ⟨Q, ?_, ?_⟩
  · intro σ
    rw [show Q σ = -(QM σ + QH σ + QS σ) from rfl, MvPolynomial.totalDegree_neg]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le _ ((hQS σ).trans (by omega))
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hQM σ) (hQH σ))
  · intro Y hY d
    have hget : (List.ofFn d)[0]! = d 0 := by
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn,
        dite_eq_left (by omega : 0 < m + 1), Option.getD_some]
      rfl
    have herase : (List.ofFn d).eraseIdx 0 = List.ofFn (fun i => d i.succ) := by
      rw [List.ofFn_succ]
      rfl
    simp only [adjacentCoefficient, hget, herase, map_add, hM Y hY d, hH Y hY d, hS Y hY d,
      Q, MvPolynomial.eval₂_neg, MvPolynomial.eval₂_add]
end WP.HigherOrder.KernelFiniteData
