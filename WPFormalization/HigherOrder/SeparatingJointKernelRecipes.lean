import WPFormalization.HigherOrder.JointShiftedKernelRecipes
import WPFormalization.HigherOrder.JointSmallComponentStrata
/-! Actual separating inner coefficients have joint finite-data recipes. The bounded component is eliminated by its true finite-theta polynomial and dimension support, and each remaining head is evaluated by the actual shifted affine moment identity. All low exceptions and projected degree variables are retained. The theta encoding is a finite algebra evaluation map, not an assumed formula for the amplitude. Current lower profile certificates remain the explicit induction input. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
open Set PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma smallW_stratum_encoded_polynomials (P : PsiTheory) (p q g K B : ℕ)
    (hs : Stable g (q + 1)) (hK : complexity g (q + 1) ≤ K)
    (hB : dimension g (q + 1) ≤ B) (e : Fin q → Fin p)
    (κ : KernelFiniteData.ThetaPolynomial ((3 * K) / 2 + 1) →+* R)
    (φ : ℝ → R →+* ℝ)
    (hκ : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y).comp κ =
      MvPolynomial.eval (fun i : Fin ((3 * K) / 2 + 2) => theta Y i.val)) :
    ∃ S : (Fin p → Option (Fin (B + 1))) → ℕ → R,
      (∀ σ u, dimension g (q + 1) < u → S σ u = 0) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ, ∀ u : ℕ,
        smallW P Y g (u :: List.ofFn (fun j => d (e j))) = (φ Y) (S (classify p B d) u) := by
  obtain ⟨Q, hdegree, hzero, hactual⟩ := smallW_stratum_theta_polynomials P p q g K B hs hK hB e
  refine ⟨fun σ u => κ (Q σ u), ?_, ?_⟩
  · intro σ u hu
    change κ (Q σ u) = 0
    rw [hzero σ u hu, map_zero]
  · intro Y hY d u
    rw [hactual Y hY d u, ← hκ Y hY]
    rfl

lemma actual_separating_inner_joint_recipe (P : PsiTheory) (p qs qb j K n b B D : ℕ)
    (hs : Stable j (qs + 1)) (hK : complexity j (qs + 1) ≤ K)
    (hB : b + dimension j (qs + 1) + 2 ≤ B)
    (r : ℤ) (a : Fin p → ℕ) (es : Fin qs → Fin p) (eb : Fin qb → Fin p)
    (F : ℕ → (Fin (qb + 1) → Option (Fin (b + 1))) → MvPolynomial (Fin (qb + 1)) R)
    (hdegree : ∀ i ≤ n, ∀ τ, (F i τ).totalDegree ≤ D) (φ : ℝ → R →+* ℝ)
    (hactual : ∀ i ≤ n, ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ v : Fin (qb + 1) → ℕ,
      profileCoefficient P Y (List.ofFn v) i =
        MvPolynomial.eval₂ (φ Y) (fun k => (v k : ℝ)) (F i (classify (qb + 1) b v)))
    (κ : KernelFiniteData.ThetaPolynomial ((3 * K) / 2 + 1) →+* R)
    (hκ : ∀ Y ∈ Icc (0 : ℝ) y₀, (φ Y).comp κ =
      MvPolynomial.eval (fun i : Fin ((3 * K) / 2 + 2) => theta Y i.val))
    (M W : ℕ → R)
    (hm : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ k : ℕ, k ≤ D →
      HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) ((φ Y) (M k)))
    (hw : ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ l : ℕ, l < b + dimension j (qs + 1) + 3 →
      weight Y l = (φ Y) (W l)) :
    ∃ Q : (Fin p → Option (Fin (B + 1))) → MvPolynomial (Fin p) R,
      (∀ σ, (Q σ).totalDegree ≤ D) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ,
        PowerSeries.coeff n (coefficientSum (fun l : ℕ => C (weight Y l) *
          ∑ u ∈ Finset.range ((∑ i : Fin p, a i * d i) + l - 1),
            C (smallW P Y j (u :: List.ofFn (fun k => d (es k)))) *
              complexityShift (r : ℝ) (formalProfile P Y
                (((∑ i : Fin p, a i * d i) + l - 2 - u) :: List.ofFn (fun k => d (eb k)))))) =
          MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify p B d)) := by
  obtain ⟨S, hzero, hsmall⟩ := smallW_stratum_encoded_polynomials P p qs j K B hs hK (by omega) es κ φ hκ
  let Q : (Fin p → Option (Fin (B + 1))) → MvPolynomial (Fin p) R := fun σ =>
    ∑ u ∈ Finset.range (dimension j (qs + 1) + 1),
      MvPolynomial.C (S σ u) * affineShiftMomentPolynomial b (u + 2) B n r a σ eb F M W
  refine ⟨Q, ?_, ?_⟩
  · intro σ
    apply MvPolynomial.totalDegree_finsetSum_le
    intro u hu
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact affineShiftMomentPolynomial_degree b (u + 2) B n D r a σ eb F hdegree M W
  · intro Y hY d
    have huhead (u : ℕ) (hu : u ∈ Finset.range (dimension j (qs + 1) + 1)) :=
      actual_affine_shifted_kernel_recipe P p qb n b (u + 2) B D (by
        have := Finset.mem_range.mp hu
        omega) r a eb F hdegree φ hactual M W weight hm (by
          intro Z hZ l hl
          apply hw Z hZ l
          have := Finset.mem_range.mp hu
          omega) Y hY d
    have hsum := hasSum_sum (s := Finset.range (dimension j (qs + 1) + 1)) (fun u hu =>
      (huhead u hu).mul_left (smallW P Y j (u :: List.ofFn (fun k => d (es k)))))
    rw [coefficientSum_coeff]
    calc
      _ = ∑' l : ℕ, ∑ u ∈ Finset.range (dimension j (qs + 1) + 1),
          smallW P Y j (u :: List.ofFn (fun k => d (es k))) *
            (weight Y l * (if u + 2 ≤ (∑ i : Fin p, a i * d i) + l then
              PowerSeries.coeff n (complexityShift (r : ℝ) (formalProfile P Y
                (((∑ i : Fin p, a i * d i) + l - (u + 2)) :: List.ofFn (fun k => d (eb k))))) else 0)) := by
        congr 1
        funext l
        rw [PowerSeries.coeff_C_mul, separating_kernel_finite_component_support]
        simp only [List.length_ofFn, map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hv : u + 2 ≤ (∑ i : Fin p, a i * d i) + l
        · simp only [ite_eq_left hv, PowerSeries.coeff_C_mul]
          have he : (∑ i : Fin p, a i * d i) + l - 2 - u =
              (∑ i : Fin p, a i * d i) + l - (u + 2) := by omega
          rw [he]
          ring
        · simp only [ite_eq_right hv, map_zero, mul_zero]
      _ = ∑ u ∈ Finset.range (dimension j (qs + 1) + 1),
          smallW P Y j (u :: List.ofFn (fun k => d (es k))) *
            MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ))
              (affineShiftMomentPolynomial b (u + 2) B n r a (classify p B d) eb F M W) := hsum.tsum_eq
      _ = MvPolynomial.eval₂ (φ Y) (fun i => (d i : ℝ)) (Q (classify p B d)) := by
        simp only [Q, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
        apply Finset.sum_congr rfl
        intro u hu
        rw [hsmall Y hY d u]
end WP.HigherOrder.JointBoundary
