import Mathlib
/-! A finite multivariate polynomial is contracted against finitely many actual moments. This explicit operation preserves total degree in the remaining variables. Its weighted HasSum identity uses only moment orders up to the stated degree, and permits a polynomial coefficient ring with a real evaluation homomorphism. -/
noncomputable section
namespace WP.HigherOrder.BoundaryPolynomial
variable {R : Type*} [CommRing R]

def dropMomentVariable {p : ℕ} (m : Option (Fin p) →₀ ℕ) : Fin p →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (some i))

@[simp] lemma dropMomentVariable_apply {p : ℕ} (m : Option (Fin p) →₀ ℕ) (i : Fin p) :
    dropMomentVariable m i = m (some i) := by simp [dropMomentVariable]

lemma monomialTotal_eq {p : ℕ} (m : Option (Fin p) →₀ ℕ) :
    m.sum (fun _ e => e) = m none + ∑ i : Fin p, m (some i) := by
  rw [Finsupp.sum_fintype m (fun _ e => e) (fun _ => rfl), Fintype.sum_option]

lemma dropMomentVariable_total {p : ℕ} (m : Option (Fin p) →₀ ℕ) :
    (dropMomentVariable m).sum (fun _ e => e) = ∑ i : Fin p, m (some i) := by
  rw [Finsupp.sum_fintype _ (fun _ e => e) (fun _ => rfl)]
  simp only [dropMomentVariable_apply]

def momentContraction {p : ℕ} (M : ℕ → R) (F : MvPolynomial (Option (Fin p)) R) : MvPolynomial (Fin p) R :=
  ∑ m ∈ F.support, MvPolynomial.monomial (dropMomentVariable m) (F.coeff m * M (m none))

lemma momentContraction_degree {p : ℕ} (M : ℕ → R) (F : MvPolynomial (Option (Fin p)) R) :
    (momentContraction M F).totalDegree ≤ F.totalDegree := by
  unfold momentContraction
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have he := MvPolynomial.le_totalDegree hm
  rw [monomialTotal_eq] at he
  change (dropMomentVariable m).sum (fun _ e => e) ≤ F.totalDegree
  rw [dropMomentVariable_total]
  omega

lemma momentContraction_eval {p : ℕ} (M : ℕ → R) (F : MvPolynomial (Option (Fin p)) R)
    (φ : R →+* ℝ) (x : Fin p → ℝ) :
    (momentContraction M F).eval₂ φ x =
      ∑ m ∈ F.support, φ (F.coeff m) * φ (M (m none)) * ∏ i : Fin p, x i ^ m (some i) := by
  simp only [momentContraction, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial, map_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finsupp.prod_fintype _ (fun i e => x i ^ e) (fun i => pow_zero _)]
  simp only [dropMomentVariable_apply]

lemma momentContraction_hasSum {p : ℕ} (M : ℕ → R) (F : MvPolynomial (Option (Fin p)) R)
    (φ : R →+* ℝ) (x : Fin p → ℝ) (w : ℕ → ℝ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (hm : ∀ j : ℕ, j ≤ D → HasSum (fun l : ℕ => (l : ℝ) ^ j * w l) (φ (M j))) :
    HasSum (fun l : ℕ => w l * F.eval₂ φ (fun i => i.elim (l : ℝ) x))
      ((momentContraction M F).eval₂ φ x) := by
  have hs : HasSum (fun l : ℕ => ∑ m ∈ F.support,
      (φ (F.coeff m) * ∏ i : Fin p, x i ^ m (some i)) * ((l : ℝ) ^ m none * w l))
      (∑ m ∈ F.support, (φ (F.coeff m) * ∏ i : Fin p, x i ^ m (some i)) * φ (M (m none))) := by
    apply hasSum_sum
    intro m hmF
    have hbound : m none ≤ D := by
      have ht := (MvPolynomial.le_totalDegree hmF).trans hD
      rw [monomialTotal_eq] at ht
      omega
    exact (hm (m none) hbound).mul_left _
  convert! hs using 1
  · funext l
    rw [MvPolynomial.eval₂_eq', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hmF
    rw [Fintype.prod_option]
    change w l * (φ (F.coeff m) * ((l : ℝ) ^ m none * ∏ i : Fin p, x i ^ m (some i))) = _
    ring
  · rw [momentContraction_eval]
    apply Finset.sum_congr rfl
    intro m hmF
    ring
end WP.HigherOrder.BoundaryPolynomial
