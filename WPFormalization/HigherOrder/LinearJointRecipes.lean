import WPFormalization.HigherOrder.FiniteScalarFront
import WPFormalization.HigherOrder.MergerTuple
import WPFormalization.HigherOrder.JointShiftedKernelRecipes
/-! Joint finite-data recipes for the full actual canonical merger and nonseparating contributions. The true scalar factors, fixed integer shifts, all merger labels and eraseIdx tuples are retained. Strictly lower profile/cusp/genus stratum inputs and finite actual kernel data suffice; degrees are at most D+1. This is an inductive step, not the all-order stratum existence theorem. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open PowerSeries
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]
def handleFrontRecipe (A : R) (c g : ℕ → R) (n : ℕ) : R :=
  scalarProductRecipe (linearFrontRecipe (2 * A) c) g n

lemma handleFrontRecipe_zero (A : R) (c g : ℕ → R) : handleFrontRecipe A c g 0 = 0 :=
  scalarProductRecipe_zero _ _ (linearFrontRecipe_zero _ _)

def handleContributionRecipe {p q : ℕ} (n b B : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (A : R) (c g M W : ℕ → R) : MvPolynomial (Fin p) R :=
  scalarKernelConvolution n (handleFrontRecipe A c g)
    (fun i => affinePairShiftMomentPolynomial b B i 1 a σ e F M W)

lemma handleContributionRecipe_degree {p q : ℕ} (n b B D : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (hdegree : ∀ i < n, ∀ τ, (F i τ).totalDegree ≤ D)
    (A : R) (c g M W : ℕ → R) :
    (handleContributionRecipe n b B a σ e F A c g M W).totalDegree ≤ D + 1 := by
  apply scalarKernelConvolution_degree _ _ _ _ (handleFrontRecipe_zero _ _ _)
  intro i hi
  exact affinePairShiftMomentPolynomial_degree b B i D 1 a σ e F
    (fun j hj => hdegree j (by omega)) M W

lemma actual_nonseparating_contribution_recipe (P : PsiTheory) (p q n b B D : ℕ)
    (hB : 2 * b + 2 ≤ B) (a : Fin p → ℕ) (e : Fin q → Fin p)
    (F : ℕ → (Fin (q + 2) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 2)) R)
    (hdegree : ∀ i < n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i < n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 2) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun j => (v j : ℝ)) (F i (classify (q + 2) b v)))
    (A : R) (c g M W : ℕ → R)
    (hA : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, (φ Y) A = WP.A Y)
    (hc : ∀ i < n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, cuspCoefficient P Y (q + 2) i = (φ Y) (c i))
    (hg : ∀ i < n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, genusCoefficient P Y (q + 1) i = (φ Y) (g i))
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D + 1 →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < 2 * b + 3 → weight Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      PowerSeries.coeff n (nonseparatingSeries Y (formalHierarchyJet P Y)
        (∑ j : Fin p, a j * d j) (List.ofFn (fun j => d (e j)))) =
        MvPolynomial.eval₂ (φ Y) (fun j => (d j : ℝ))
          (handleContributionRecipe n b B a (classify p B d) e F A c g M W) := by
  intro Y hY d
  let left : Series := C (2 * WP.A Y) * shiftVariable 1 * complexityShift 1 (formalCusp P Y (q + 2))
  let front : Series := left * formalGenus P Y (q + 1)
  let kernel : Series := coefficientSum (fun l : ℕ => C (weight Y l) *
    ∑ u ∈ Finset.range ((∑ j : Fin p, a j * d j) + l - 1),
      complexityShift 1 (formalProfile P Y
        (u :: ((∑ j : Fin p, a j * d j) + l - 2 - u) :: List.ofFn (fun j => d (e j)))))
  have hleft (k : ℕ) (hk : k ≤ n) :
      PowerSeries.coeff k left = (φ Y) (linearFrontRecipe (2 * A) c k) := by
    have hh := linearFrontRecipe_eval (2 * A) c k (φ Y) (formalCusp P Y (q + 2)) (by
      intro i hi
      simpa only [formalCusp, PowerSeries.coeff_mk] using hc i (by omega) Y hY)
    simpa only [left, map_mul, map_ofNat, hA Y hY] using hh
  have hfront (k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k front = (φ Y) (handleFrontRecipe A c g k) := by
    apply scalarProductRecipe_eval _ _ _ _ _ _ (linearFrontRecipe_zero _ _)
    · intro i hi
      exact hleft i (by omega)
    · intro i hi
      simpa only [formalGenus, PowerSeries.coeff_mk] using hg i (by omega) Y hY
  have hkernel (k : ℕ) (hk : k < n) : PowerSeries.coeff k kernel =
      MvPolynomial.eval₂ (φ Y) (fun j => (d j : ℝ))
        (affinePairShiftMomentPolynomial b B k 1 a (classify p B d) e F M W) := by
    simpa only [Int.cast_one] using
      actual_affine_handle_kernel_coefficient_recipe P p q k b B D hB 1 a e F
        (fun i hi => hdegree i (by omega)) φ (fun i hi => hactual i (by omega))
        M W weight hm hw Y hY d
  have he := scalarKernelConvolution_eval n (handleFrontRecipe A c g)
    (fun i => affinePairShiftMomentPolynomial b B i 1 a (classify p B d) e F M W)
    (handleFrontRecipe_zero _ _ _) (φ Y) (fun j => (d j : ℝ)) front kernel hfront hkernel
  simpa only [handleContributionRecipe, front, left, kernel, nonseparatingSeries,
    formalHierarchyJet, List.length_ofFn] using he


def mergerLabel {p : ℕ} (j : Fin p) : MvPolynomial (Fin p) R :=
  MvPolynomial.C (2 : R) * MvPolynomial.X j + 1

lemma mergerLabel_degree {p : ℕ} (j : Fin p) : (mergerLabel j : MvPolynomial (Fin p) R).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le _ (by simp)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact variable_degree_le_one _

lemma mergerLabel_eval {p : ℕ} (j : Fin p) (φ : R →+* ℝ) (d : Fin p → ℕ) :
    MvPolynomial.eval₂ φ (fun i => (d i : ℝ)) (mergerLabel j) = 2 * (d j : ℝ) + 1 := by
  have ht : φ (2 : R) = (2 : ℝ) := map_ofNat φ 2
  simp [mergerLabel, ht]

def mergerContributionRecipe {p q : ℕ} (n b B : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p) (j : Fin p)
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (A : R) (c M W : ℕ → R) : MvPolynomial (Fin p) R :=
  scalarKernelConvolution n (linearFrontRecipe A c)
    (fun i => mergerLabel j * affineShiftMomentPolynomial b 1 B i 1 a σ e F M W)

lemma mergerContributionRecipe_degree {p q : ℕ} (n b B D : ℕ) (a : Fin p → ℕ)
    (σ : Fin p → Option (Fin (B + 1))) (e : Fin q → Fin p) (j : Fin p)
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ i < n, ∀ τ, (F i τ).totalDegree ≤ D)
    (A : R) (c M W : ℕ → R) :
    (mergerContributionRecipe n b B a σ e j F A c M W).totalDegree ≤ D + 1 := by
  apply scalarKernelConvolution_degree _ _ _ _ (linearFrontRecipe_zero _ _)
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hh := affineShiftMomentPolynomial_degree b 1 B i D 1 a σ e F
    (fun k hk => hdegree k (by omega)) M W
  exact (add_le_add (mergerLabel_degree j) hh).trans_eq (Nat.add_comm 1 D)

lemma actual_merger_contribution_recipe (P : PsiTheory) (p q n b B D : ℕ)
    (hB : b + 1 ≤ B) (a : Fin p → ℕ) (e : Fin q → Fin p) (j : Fin p)
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ i < n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i < n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun k => (v k : ℝ)) (F i (classify (q + 1) b v)))
    (A : R) (c M W : ℕ → R)
    (hA : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, (φ Y) A = WP.A Y)
    (hc : ∀ i < n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, cuspCoefficient P Y (q + 1) i = (φ Y) (c i))
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < b + 2 → weight Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
      PowerSeries.coeff n (C (WP.A Y) * shiftVariable 1 * complexityShift 1 (formalCusp P Y (q + 1)) *
        C (2 * (d j : ℝ) + 1) * coefficientSum (fun l : ℕ =>
          if 1 ≤ (∑ k : Fin p, a k * d k) + l then
            C (weight Y l) * complexityShift 1 (formalProfile P Y
              (((∑ k : Fin p, a k * d k) + l - 1) :: List.ofFn (fun k => d (e k)))) else 0)) =
        MvPolynomial.eval₂ (φ Y) (fun k => (d k : ℝ))
          (mergerContributionRecipe n b B a (classify p B d) e j F A c M W) := by
  intro Y hY d
  let front : Series := C (WP.A Y) * shiftVariable 1 * complexityShift 1 (formalCusp P Y (q + 1))
  let kernel : Series := C (2 * (d j : ℝ) + 1) * coefficientSum (fun l : ℕ =>
    if 1 ≤ (∑ k : Fin p, a k * d k) + l then
      C (weight Y l) * complexityShift 1 (formalProfile P Y
        (((∑ k : Fin p, a k * d k) + l - 1) :: List.ofFn (fun k => d (e k)))) else 0)
  have hfront (k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k front = (φ Y) (linearFrontRecipe A c k) := by
    have hh := linearFrontRecipe_eval A c k (φ Y) (formalCusp P Y (q + 1)) (by
      intro i hi
      simpa only [formalCusp, PowerSeries.coeff_mk] using hc i (by omega) Y hY)
    simpa only [hA Y hY] using hh
  have hkernel (k : ℕ) (hk : k < n) : PowerSeries.coeff k kernel =
      MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ))
        (mergerLabel j * affineShiftMomentPolynomial b 1 B k 1 a (classify p B d) e F M W) := by
    change PowerSeries.coeff k (C (2 * (d j : ℝ) + 1) * _) = _
    rw [PowerSeries.coeff_C_mul, MvPolynomial.eval₂_mul, mergerLabel_eval]
    congr 1
    simpa only [Int.cast_one, Nat.add_assoc] using
      actual_affine_merger_kernel_coefficient_recipe P p q k b 1 B D hB 1 a e F
        (fun i hi => hdegree i (by omega)) φ (fun i hi => hactual i (by omega))
        M W weight hm hw Y hY d
  have he := scalarKernelConvolution_eval n (linearFrontRecipe A c)
    (fun i => mergerLabel j * affineShiftMomentPolynomial b 1 B i 1 a (classify p B d) e F M W)
    (linearFrontRecipe_zero _ _) (φ Y) (fun k => (d k : ℝ)) front kernel hfront hkernel
  simpa only [mergerContributionRecipe, front, kernel, mul_assoc] using he
end WP.HigherOrder.KernelFiniteData
namespace WP.HigherOrder.KernelFiniteData
open PowerSeries
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]
def mergerSeriesJointRecipe (q n b B : ℕ) (σ : Fin (q + 2) → Option (Fin (B + 1)))
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (A : R) (c M W : ℕ → R) : MvPolynomial (Fin (q + 2)) R :=
  ∑ j : Fin (q + 1), mergerContributionRecipe n b B
    (mergerHeadCoefficients j) σ (mergerRemainingIndex j) j.succ F A c M W

lemma mergerSeriesJointRecipe_degree (q n b B D : ℕ)
    (σ : Fin (q + 2) → Option (Fin (B + 1)))
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ i < n, ∀ τ, (F i τ).totalDegree ≤ D)
    (A : R) (c M W : ℕ → R) :
    (mergerSeriesJointRecipe q n b B σ F A c M W).totalDegree ≤ D + 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact mergerContributionRecipe_degree _ _ _ _ _ _ _ _ _ hdegree _ _ _ _

lemma actual_merger_series_joint_recipe (P : PsiTheory) (q n b B D : ℕ)
    (hB : b + 1 ≤ B)
    (F : ℕ → (Fin (q + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (q + 1)) R)
    (hdegree : ∀ i < n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i < n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ v : Fin (q + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun k => (v k : ℝ)) (F i (classify (q + 1) b v)))
    (A : R) (c M W : ℕ → R)
    (hA : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, (φ Y) A = WP.A Y)
    (hc : ∀ i < n, ∀ Y ∈ Set.Icc (0 : ℝ) y₀, cuspCoefficient P Y (q + 1) i = (φ Y) (c i))
    (hm : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ l : ℕ, l < b + 2 → weight Y l = (φ Y) (W l)) :
    ∀ Y ∈ Set.Icc (0 : ℝ) y₀, ∀ d : Fin (q + 2) → ℕ,
      PowerSeries.coeff n (mergerSeries Y (formalHierarchyJet P Y)
        (d 0) (List.ofFn (fun i => d i.succ))) =
        MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ))
          (mergerSeriesJointRecipe q n b B (classify (q + 2) B d) F A c M W) := by
  intro Y hY d
  simp only [mergerSeries, formalHierarchyJet, List.length_ofFn, Finset.mul_sum, map_sum,
    mergerSeriesJointRecipe, MvPolynomial.eval₂_sum]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have he := actual_merger_contribution_recipe P (q + 2) q n b B D hB
    (mergerHeadCoefficients j) (mergerRemainingIndex j) j.succ F hdegree φ hactual
    A c M W hA hc hm hw Y hY d
  have hget : (List.ofFn (fun i : Fin (q + 1) => d i.succ))[j.val]! = d j.succ := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left j.isLt, Option.getD_some]
  have herase := eraseIdx_ofFn_eq (fun i : Fin (q + 1) => d i.succ) j
  simpa only [mergerHeadCoefficients_sum, mergerRemainingIndex, herase, hget, mul_assoc] using he
end WP.HigherOrder.KernelFiniteData
