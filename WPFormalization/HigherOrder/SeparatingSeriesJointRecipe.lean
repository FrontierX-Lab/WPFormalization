import WPFormalization.HigherOrder.SelectedTuple
import WPFormalization.HigherOrder.SeparatingJointContribution
/-! The full actual canonical separatingSeries coefficient has a joint finite-data recipe, including every genus/subset label, selectedNat order, complement and eligibility branch. Only strictly lower profile/cusp/genus recipes and actual finite kernel data are used. The degree bound is D and the cutoff is uniform before the parameter and every degree tuple. This is an induction step, not an all-order certificate. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set PowerSeries
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma actual_separating_series_joint_recipe (P : PsiTheory) (m K b B D : ℕ)
    (hB : b + (3 * K) / 2 + 2 ≤ B)
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
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ l : ℕ, l < b + (3 * K) / 2 + 3 → weight Y l = (φ Y) (W l)) :
    ∃ Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R,
      (∀ σ, (Q σ).totalDegree ≤ D) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
        PowerSeries.coeff K (separatingSeries P Y (formalHierarchyJet P Y) K
          (d 0) (List.ofFn (fun i : Fin m => d i.succ))) =
          MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify (m + 1) B d)) := by
  have hpart (j : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range m)
      (hel : Stable j (I.card + 1) ∧ 2 ≤ 2 * j + I.card ∧ 2 * j + I.card ≤ K) :
      ∃ Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R,
        (∀ σ, (Q σ).totalDegree ≤ D) ∧
        ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin (m + 1) → ℕ,
          PowerSeries.coeff K (ratioSeries Y (formalHierarchyJet P Y) (m + 1) j I.card *
            coefficientSum (fun l => C (weight Y l) *
              ∑ u ∈ Finset.range (d 0 + l - 1),
                C (smallW P Y j (u :: selectedNat (List.ofFn (fun i : Fin m => d i.succ)) I)) *
                  complexityShift (2 * j + I.card) (formalProfile P Y
                    ((d 0 + l - 2 - u) :: selectedNat (List.ofFn (fun i : Fin m => d i.succ)) ((Finset.range m) \ I))))) =
            MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify (m + 1) B d)) := by
    have hcomp : complexity j (I.card + 1) ≤ K := by unfold complexity; omega
    have hdim : dimension j (I.card + 1) ≤ (3 * K) / 2 := by
      unfold dimension complexity Stable at *
      omega
    let J := (Finset.range m) \ I
    have hJ : J ⊆ Finset.range m := Finset.sdiff_subset
    obtain ⟨Q, hdeg, hval⟩ := actual_separating_contribution_recipe P (m + 1) I.card J.card j K b B D
      hel.1 hel.2.1 hel.2.2 (by omega) (pivotHeadCoefficients m)
      (selectedSubsetProjection m I hI) (selectedSubsetProjection m J hJ) (F J.card)
      (hdegree J.card) φ (hactual J.card) A c g hA hc hg κ hκ M W hm (by
        intro Y hY l hl
        apply hw Y hY l
        omega)
    refine ⟨Q, hdeg, ?_⟩
    intro Y hY d
    have he := hval Y hY d
    have hsize : I.card + J.card + 1 = m + 1 := by
      have hh := selection_complement_card m I hI
      change I.card + J.card = m at hh
      omega
    simpa only [pivotHeadCoefficients_sum, selectedNat_ofFn_subset_projection, hsize,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using he
  let part : ℕ → Finset ℕ → (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R :=
    fun j I σ => if hI : I ⊆ Finset.range m then
      if hel : Stable j (I.card + 1) ∧ 2 ≤ 2 * j + I.card ∧ 2 * j + I.card ≤ K then
        Classical.choose (hpart j I hI hel) σ else 0 else 0
  let Q : (Fin (m + 1) → Option (Fin (B + 1))) → MvPolynomial (Fin (m + 1)) R := fun σ =>
    ∑ j ∈ Finset.range (K + 1), ∑ I ∈ (Finset.range m).powerset, part j I σ
  refine ⟨Q, ?_, ?_⟩
  · intro σ
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply MvPolynomial.totalDegree_finsetSum_le
    intro I hI
    dsimp only [part]
    split_ifs with hsub hel
    · exact (Classical.choose_spec (hpart j I hsub hel)).1 σ
    · simp
    · simp
  · intro Y hY d
    simp only [separatingSeries, formalHierarchyJet, List.length_ofFn, map_sum,
      Q, MvPolynomial.eval₂_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro I hI
    have hsub : I ⊆ Finset.range m := Finset.mem_powerset.mp hI
    dsimp only [part]
    rw [dite_eq_left hsub]
    by_cases hel : Stable j (I.card + 1) ∧ 2 ≤ 2 * j + I.card ∧ 2 * j + I.card ≤ K
    · rw [ite_eq_left hel, dite_eq_left hel]
      exact (Classical.choose_spec (hpart j I hsub hel)).2 Y hY d
    · rw [ite_eq_right hel, dite_eq_right hel]
      simp
end WP.HigherOrder.KernelFiniteData
