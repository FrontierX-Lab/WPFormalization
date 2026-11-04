import WPFormalization.HigherOrder.FiniteRatioRecipe
import WPFormalization.HigherOrder.SeparatingJointKernelRecipes
/-! The actual separating contribution, including its complete finite scalar ratio, has a joint finite-data polynomial recipe. The bounded amplitude is obtained from actual theta data and dimension support. Current profile/cusp/genus inputs are strictly lower order; the positive ratio loss fixes its algebraic zero constant. All degree variables and the closed critical restriction are retained. The all-order input certificates are not asserted here. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set PowerSeries
open JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma actual_separating_contribution_recipe (P : PsiTheory) (p qs qb j n b B D : ℕ)
    (hs : Stable j (qs + 1)) (hr : 2 ≤ 2 * j + qs) (hrn : 2 * j + qs ≤ n)
    (hB : b + dimension j (qs + 1) + 2 ≤ B)
    (a : Fin p → ℕ) (es : Fin qs → Fin p) (eb : Fin qb → Fin p)
    (F : ℕ → (Fin (qb + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (qb + 1)) R)
    (hdegree : ∀ i < n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i < n, ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ v : Fin (qb + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun k => (v k : ℝ)) (F i (classify (qb + 1) b v)))
    (A : R) (c g : ℕ → ℕ → R)
    (hA : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y) A = WP.A Y)
    (hc : ∀ q ≥ 1, ∀ i < n, ∀ Y ∈ Icc (0 : ℝ) y₀, cuspCoefficient P Y q i = (φ Y) (c q i))
    (hg : ∀ q ≥ 1, ∀ i < n, ∀ Y ∈ Icc (0 : ℝ) y₀, genusCoefficient P Y q i = (φ Y) (g q i))
    (κ : ThetaPolynomial ((3 * n) / 2 + 1) →+* R)
    (hκ : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y).comp κ =
      MvPolynomial.eval (fun i : Fin ((3 * n) / 2 + 2) => theta Y i.val))
    (M W : ℕ → R)
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ l : ℕ, l < b + dimension j (qs + 1) + 3 →
      weight Y l = (φ Y) (W l)) :
    ∃ Q : (Fin p → Option (Fin (B + 1))) → MvPolynomial (Fin p) R,
      (∀ σ, (Q σ).totalDegree ≤ D) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
        PowerSeries.coeff n (ratioSeries Y (formalHierarchyJet P Y) (qs + qb + 1) j qs *
          coefficientSum (fun l : ℕ => C (weight Y l) *
            ∑ u ∈ Finset.range ((∑ i : Fin p, a i * d i) + l - 1),
              C (smallW P Y j (u :: List.ofFn (fun k => d (es k)))) *
                complexityShift ((2 * j + qs : ℕ) : ℝ) (formalProfile P Y
                  (((∑ i : Fin p, a i * d i) + l - 2 - u) :: List.ofFn (fun k => d (eb k)))))) =
          MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify p B d)) := by
  have hcomp : complexity j (qs + 1) ≤ n := by unfold complexity; omega
  let inner : ℝ → (Fin p → ℕ) → Series := fun Y d =>
    coefficientSum (fun l : ℕ => C (weight Y l) *
      ∑ u ∈ Finset.range ((∑ i : Fin p, a i * d i) + l - 1),
        C (smallW P Y j (u :: List.ofFn (fun k => d (es k)))) *
          complexityShift ((2 * j + qs : ℕ) : ℝ) (formalProfile P Y
            (((∑ i : Fin p, a i * d i) + l - 2 - u) :: List.ofFn (fun k => d (eb k)))))
  have hi (k : ℕ) (hk : k < n) :
      ∃ Q : (Fin p → Option (Fin (B + 1))) → MvPolynomial (Fin p) R,
        (∀ σ, (Q σ).totalDegree ≤ D) ∧
        ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
          PowerSeries.coeff k (inner Y d) = MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify p B d)) := by
    simpa only [inner, Int.cast_natCast] using actual_separating_inner_joint_recipe
      P p qs qb j n k b B D hs hcomp hB ((2 * j + qs : ℕ) : ℤ) a es eb F
      (fun i hik => hdegree i (by omega)) φ (fun i hik => hactual i (by omega))
      κ hκ M W hm hw
  let Qinner : ℕ → (Fin p → Option (Fin (B + 1))) → MvPolynomial (Fin p) R :=
    fun k σ => if hk : k < n then Classical.choose (hi k hk) σ else 0
  let Q : (Fin p → Option (Fin (B + 1))) → MvPolynomial (Fin p) R := fun σ =>
    scalarKernelConvolution n (ratioCoefficientRecipe A c g (qs + qb + 1) j qs)
      (fun k => Qinner k σ)
  refine ⟨Q, ?_, ?_⟩
  · intro σ
    apply scalarKernelConvolution_degree _ _ _ _ (ratioCoefficientRecipe_zero _ _ _ _ _ _ (by omega))
    intro k hk
    dsimp only [Qinner]
    rw [dite_eq_left hk]
    exact (Classical.choose_spec (hi k hk)).1 σ
  · intro Y hY d
    apply scalarKernelConvolution_eval _ _ _ (ratioCoefficientRecipe_zero _ _ _ _ _ _ (by omega))
    · intro k hk
      exact ratioCoefficientRecipe_eval P Y A c g (qs + qb + 1) j qs n k (φ Y)
        (by omega) (by omega) (by omega) hk (hA Y hY)
        (fun q hq i hi => hc q hq i hi Y hY) (fun q hq i hi => hg q hq i hi Y hY)
    · intro k hk
      dsimp only [Qinner]
      rw [dite_eq_left hk]
      exact (Classical.choose_spec (hi k hk)).2 Y hY d
end WP.HigherOrder.KernelFiniteData
