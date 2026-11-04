import WPFormalization.HigherOrder.JointDiagonalBoundary
import WPFormalization.HigherOrder.BoundarySummation
/-! Actual canonical nonseparating heads have joint finite-data recipes from the current child certificate. All totals at most 2b are explicit finite exceptions; larger totals use both boundary corrections. Parent cutoff B≥2b+2, moments through D+1 and low weights through 2b+2 suffice uniformly before all degrees and Y. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]
def diagonalBoundaryTail {p : ℕ} (b : ℕ)
    (σ : Fin (p + 1) → Option (Fin (2 * b + 1))) : Fin p → Option (Fin (b + 1)) :=
  affineTailPattern b (2 * b) σ Fin.succ

def jointDiagonalBoundary {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (σ : Fin (p + 1) → Option (Fin (2 * b + 1))) : MvPolynomial (Fin (p + 1)) R :=
  match σ 0 with
  | some k => ∑ u ∈ Finset.range (k.val + 1),
      pairSlot (MvPolynomial.C (u : R)) (MvPolynomial.C ((k.val - u : ℕ) : R))
        (F (Fin.cases (classify 1 b (fun _ => u) 0)
          (Fin.cases (classify 1 b (fun _ => k.val - u) 0) (diagonalBoundaryTail b σ))))
  | none => jointPairEventualPolynomial b
      (F (Fin.cases none (Fin.cases none (diagonalBoundaryTail b σ))))
      (fun a => pairSlot (MvPolynomial.C (a : R)) (MvPolynomial.X 0)
        (F (Fin.cases (classify 1 b (fun _ => a) 0)
          (Fin.cases none (diagonalBoundaryTail b σ)))))
      (fun a => pairSlot (MvPolynomial.X 0) (MvPolynomial.C (a : R))
        (F (Fin.cases none
          (Fin.cases (classify 1 b (fun _ => a) 0) (diagonalBoundaryTail b σ)))))

lemma jointDiagonalBoundary_degree {p : ℕ} (b D : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D)
    (σ : Fin (p + 1) → Option (Fin (2 * b + 1))) :
    (jointDiagonalBoundary b F σ).totalDegree ≤ D + 1 := by
  unfold jointDiagonalBoundary
  split
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro u hu
    exact ((pairSlot_degree _ _ _ (by rw [MvPolynomial.totalDegree_C]; omega)
      (by rw [MvPolynomial.totalDegree_C]; omega)).trans (hdegree _)).trans (by omega)
  · apply jointPairEventualPolynomial_degree
    · exact hdegree _
    · intro a ha
      exact (pairSlot_degree _ _ _ (by rw [MvPolynomial.totalDegree_C]; omega)
        (variable_degree_le_one _)).trans (hdegree _)
    · intro a ha
      exact (pairSlot_degree _ _ _ (variable_degree_le_one _)
        (by rw [MvPolynomial.totalDegree_C]; omega)).trans (hdegree _)

lemma jointDiagonalBoundary_eval {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (d : Fin (p + 1) → ℕ) :
    MvPolynomial.eval (fun j => (d j : R)) (jointDiagonalBoundary b F (classify (p + 1) (2 * b) d)) =
      ∑ u ∈ Finset.range (d 0 + 1),
        profileRecipeValue b F (Fin.cases u (Fin.cases (d 0 - u) (fun j => d j.succ))) := by
  have htail : diagonalBoundaryTail b (classify (p + 1) (2 * b) d) =
      classify p b (fun j => d j.succ) :=
    affineTailPattern_classify b (2 * b) (by omega) d Fin.succ
  have hcast : (fun j => (d j : R)) = Fin.cases (d 0 : R) (fun j => (d j.succ : R)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  by_cases hd : d 0 ≤ 2 * b
  · have hs : classify (p + 1) (2 * b) d 0 = some (⟨d 0, by omega⟩ : Fin (2 * b + 1)) := by
      simp only [classify, dite_eq_left hd]
    unfold jointDiagonalBoundary
    rw [hs, map_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [pairSlot_eval]
    simp only [MvPolynomial.eval_C]
    unfold profileRecipeValue
    rw [classify_pair, cast_pair, htail]
  · have hs : classify (p + 1) (2 * b) d 0 = none := by simp only [classify, dite_eq_right hd]
    unfold jointDiagonalBoundary
    rw [hs, hcast]
    apply jointPairEventualPolynomial_eval b (d 0) _ _ _ _
      (fun u v => profileRecipeValue b F (Fin.cases u (Fin.cases v (fun j => d j.succ)))) (by omega)
    · intro u v huv hu hv
      unfold profileRecipeValue
      rw [classify_pair, cast_pair, htail]
      simp only [classify, not_le.mpr hu, not_le.mpr hv, dite_false]
    · intro a ha
      have hv : b < d 0 - a := by omega
      rw [pairSlot_eval]
      simp only [MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.cases_zero, Fin.cases_succ]
      unfold profileRecipeValue
      rw [classify_pair, cast_pair, htail]
      simp only [classify, not_le.mpr hv, dite_false]
    · intro a ha
      have hu : b < d 0 - a := by omega
      rw [pairSlot_eval]
      simp only [MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.cases_zero, Fin.cases_succ]
      unfold profileRecipeValue
      rw [classify_pair, cast_pair, htail]
      simp only [classify, not_le.mpr hu, dite_false]


lemma jointDiagonalBoundary_actual_eval {p : ℕ} (b : ℕ)
    (F : (Fin (p + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (p + 2)) R)
    (φ : R →+* ℝ) (f : (Fin (p + 2) → ℕ) → ℝ)
    (hactual : ∀ v : Fin (p + 2) → ℕ,
      f v = MvPolynomial.eval₂ φ (fun j => (v j : ℝ)) (F (classify (p + 2) b v)))
    (d : Fin (p + 1) → ℕ) :
    (∑ u ∈ Finset.range (d 0 + 1),
      f (Fin.cases u (Fin.cases (d 0 - u) (fun j => d j.succ)))) =
      MvPolynomial.eval₂ φ (fun j => (d j : ℝ))
        (jointDiagonalBoundary b F (classify (p + 1) (2 * b) d)) := by
  rw [← map_eval_nat, jointDiagonalBoundary_eval, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [profileRecipeValue_eval]
  exact hactual _

def affinePairMomentPolynomial {p q : ℕ} (b B : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (M W : ℕ → R) : MvPolynomial (Fin p) R :=
  affineMomentPolynomial (2 * b) 2 B a σ e (jointDiagonalBoundary b F) M W

lemma affinePairMomentPolynomial_degree {p q : ℕ} (b B D : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D) (M W : ℕ → R) :
    (affinePairMomentPolynomial b B a σ e F M W).totalDegree ≤ D + 1 := by
  exact affineMomentPolynomial_degree _ _ _ _ _ _ _ _
    (jointDiagonalBoundary_degree b D F hdegree) M W

lemma actual_profile_affine_pair_moment_recipe (P : PsiTheory) (p q K b B D : ℕ)
    (hB : 2 * b + 2 ≤ B) (a : Fin p → ℕ) (e : Fin q → Fin p)
    (F : (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 2) → ℕ,
      profileCoefficient P Y (List.ofFn v) K =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (F (classify (q + 2) b v)))
    (M W : ℕ → R) (w : ℝ → ℕ → ℝ)
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D + 1 →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * w Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < 2 * b + 3 → w Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      HasSum (fun l : ℕ => w Y l *
        (if 2 ≤ (∑ i : Fin p, a i * d i) + l then
          ∑ u ∈ Finset.range ((∑ i : Fin p, a i * d i) + l - 2 + 1),
            profileCoefficient P Y
              (u :: ((∑ i : Fin p, a i * d i) + l - 2 - u) ::
                List.ofFn (fun j => d (e j))) K else 0))
        (MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ))
          (affinePairMomentPolynomial b B a (classify p B d) e F M W)) := by
  intro Y hY d
  let f : (Fin (q + 1) → ℕ) → ℝ := fun v =>
    ∑ u ∈ Finset.range (v 0 + 1),
      profileCoefficient P Y (u :: (v 0 - u) :: List.ofFn (fun j => v j.succ)) K
  have hf : ∀ v : Fin (q + 1) → ℕ, f v =
      MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ))
        (jointDiagonalBoundary b F (classify (q + 1) (2 * b) v)) := by
    intro v
    simpa only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ] using
      jointDiagonalBoundary_actual_eval b F (φ Y)
        (fun u => profileCoefficient P Y (List.ofFn u) K) (hactual Y hY) v
  simpa only [f, Fin.cases_zero, Fin.cases_succ, affinePairMomentPolynomial] using
    affineMomentPolynomial_hasSum (2 * b) 2 B (D + 1) hB a d e
      (jointDiagonalBoundary b F) (jointDiagonalBoundary_degree b D F hdegree)
      (φ Y) f hf M W (w Y) (hm Y hY) (hw Y hY)
end WP.HigherOrder.JointBoundary
