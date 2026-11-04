import WPFormalization.HigherOrder.LinearJointRecipes
/-! The actual finite scalar ratio has a literal coefficient recipe over the kernel-data ring. All integer shifts and inverse-linear factors are evaluated genuinely; the a<r range justifies Nat.cast_sub at the real shifts. Positive loss gives algebraic constant zero and uses only strictly lower cusp/genus orders. No actual ratio is assumed as a data field. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def scalarShiftSeries (s : ℤ) (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (scalarShiftRecipe s a)

def linearInverseSeries (c : ℕ) : PowerSeries R := PowerSeries.mk (fun n => (c : R) ^ n)

lemma scalarShiftSeries_map_agree (s : ℤ) (a : ℕ → R) (N : ℕ) (φ : R →+* ℝ)
    (f : Series) (ha : ∀ i ≤ N, PowerSeries.coeff i f = φ (a i)) :
    AgreeBelow (N + 1) (PowerSeries.map φ (scalarShiftSeries s a)) (complexityShift (s : ℝ) f) := by
  intro k hk
  rw [PowerSeries.coeff_map, scalarShiftSeries, PowerSeries.coeff_mk]
  exact (scalarShiftRecipe_eval s a k φ f (fun i hi => ha i (by omega))).symm

lemma linearInverseSeries_map (c : ℕ) (φ : R →+* ℝ) :
    PowerSeries.map φ (linearInverseSeries (R := R) c) = (1 - C (c : ℝ) * PowerSeries.X)⁻¹ := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, linearInverseSeries, PowerSeries.coeff_mk, map_pow, map_natCast]
  have h := inverse_linear_pow_coeff (c : ℝ) 1 n (by omega)
  have he : 1 + n - 1 = n := by omega
  simpa only [pow_one, he, Nat.choose_self, Nat.cast_one, one_mul] using h.symm

def ratioCoreRecipeSeries (c g : ℕ → ℕ → R) (p j s : ℕ) : PowerSeries R :=
  (∏ a ∈ Finset.range (2 * j + s),
    scalarShiftSeries ((2 * j + s - a : ℕ) : ℤ) (c (p - s + a)) *
      linearInverseSeries (2 * j + s - a)) *
    ∏ b ∈ Finset.range j, PowerSeries.mk (g (p + 2 * b))

lemma ratioCoreRecipeSeries_map_agree (P : PsiTheory) (Y : ℝ)
    (c g : ℕ → ℕ → R) (p j s N : ℕ) (φ : R →+* ℝ)
    (hc : ∀ a < 2 * j + s, ∀ i ≤ N,
      cuspCoefficient P Y (p - s + a) i = φ (c (p - s + a) i))
    (hg : ∀ b < j, ∀ i ≤ N,
      genusCoefficient P Y (p + 2 * b) i = φ (g (p + 2 * b) i)) :
    AgreeBelow (N + 1) (PowerSeries.map φ (ratioCoreRecipeSeries c g p j s))
      (ratioCoreSeries (formalHierarchyJet P Y) p j s) := by
  simp only [ratioCoreRecipeSeries, ratioCoreSeries, formalHierarchyJet, map_mul, map_prod]
  apply AgreeBelow.mul
  · apply AgreeBelow.prod
    intro a ha
    rw [linearInverseSeries_map]
    apply AgreeBelow.mul _ (AgreeBelow.refl _ _)
    simpa only [Int.cast_natCast, Int.cast_sub, Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp ha))] using scalarShiftSeries_map_agree
      ((2 * j + s - a : ℕ) : ℤ) (c (p - s + a)) N φ (formalCusp P Y (p - s + a)) (by
        intro i hi
        simpa only [formalCusp, PowerSeries.coeff_mk] using hc a (Finset.mem_range.mp ha) i hi)
  · apply AgreeBelow.prod
    intro b hb
    intro i hi
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    simpa only [formalGenus, PowerSeries.coeff_mk] using (hg b (Finset.mem_range.mp hb) i (by omega)).symm

def ratioCoefficientRecipe (A : R) (c g : ℕ → ℕ → R) (p j s n : ℕ) : R :=
  if 2 * j + s ≤ n then A ^ (2 * j + s) *
    PowerSeries.coeff (n - (2 * j + s)) (ratioCoreRecipeSeries c g p j s) else 0

lemma ratioCoefficientRecipe_zero (A : R) (c g : ℕ → ℕ → R) (p j s : ℕ)
    (hr : 1 ≤ 2 * j + s) : ratioCoefficientRecipe A c g p j s 0 = 0 := by
  simp only [ratioCoefficientRecipe, ite_eq_right (by omega : ¬2 * j + s ≤ 0)]

lemma ratioCoefficientRecipe_eval (P : PsiTheory) (Y : ℝ) (A : R)
    (c g : ℕ → ℕ → R) (p j s K n : ℕ) (φ : R →+* ℝ)
    (hp : 1 ≤ p) (hs : s < p) (hr : 1 ≤ 2 * j + s) (hn : n ≤ K)
    (hA : φ A = WP.A Y)
    (hc : ∀ q ≥ 1, ∀ i < K, cuspCoefficient P Y q i = φ (c q i))
    (hg : ∀ q ≥ 1, ∀ i < K, genusCoefficient P Y q i = φ (g q i)) :
    PowerSeries.coeff n (ratioSeries Y (formalHierarchyJet P Y) p j s) =
      φ (ratioCoefficientRecipe A c g p j s n) := by
  rw [ratioSeries_coeff]
  unfold ratioCoefficientRecipe
  by_cases hnr : 2 * j + s ≤ n
  · rw [ite_eq_left hnr, ite_eq_left hnr, map_mul, map_pow, hA]
    congr 1
    have hh := ratioCoreRecipeSeries_map_agree P Y c g p j s (n - (2 * j + s)) φ
      (by intro a ha i hi; exact hc _ (by omega) i (by omega))
      (by intro b hb i hi; exact hg _ (by omega) i (by omega))
    have he := hh (n - (2 * j + s)) (by omega)
    simpa only [PowerSeries.coeff_map] using he.symm
  · simp only [ite_eq_right hnr, map_zero]
end WP.HigherOrder.KernelFiniteData
