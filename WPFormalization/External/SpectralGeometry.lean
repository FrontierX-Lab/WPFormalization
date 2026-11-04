import WPFormalization.External.HyperbolicCurveGeometry

/-! Classical spectral objects on the SAME hyperbolic surfaces as G and H.

Positive discrete eigenvalues are indexed starting at one; the constant
eigenvalue zero is excluded.  The option is `none` if that positive discrete
eigenvalue does not exist.  No geometric or spectral instance is constructed.

The deterministic many-pants field is Hide--Thomas, arXiv:2209.15568v3,
Lemma 5.3 (PDF p.26): j+1 two-cusp pants with waist length at most epsilon/6
give j positive eigenvalues at most epsilon, when 0<epsilon<1/4.  The single
pants field combines the Cheeger cut with Buser and the min--max principle,
as in Shen--Wu, arXiv:2203.15681v4, Theorems 7,11 and proof of Theorem 1
(PDF pp.35--36).  Its universal constant is not specified or fitted to the
new asymptotic result.  All fields are deterministic and have no volume
ratios, cusp-density limits or probability-one conclusion.
-/
noncomputable section
universe u v w
namespace WP.External

@[blueprint "ext:minmax"]
structure SpectralGeometry {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) where
  positiveEigenvalue : ∀ {g n : ℕ}, G.Moduli g n (fun _ => 0) → ℕ → Option ℝ
  index_zero : ∀ {g n : ℕ} (X : G.Moduli g n (fun _ => 0)), positiveEigenvalue X 0 = none
  positive : ∀ {g n : ℕ} (X : G.Moduli g n (fun _ => 0)) (j : ℕ) (ℓ : ℝ),
    positiveEigenvalue X j = some ℓ → 0 < ℓ
  initial_segment : ∀ {g n : ℕ} (X : G.Moduli g n (fun _ => 0))
    (i j : ℕ) (ν : ℝ), 1 ≤ i → i ≤ j → positiveEigenvalue X j = some ν →
      ∃ ℓ, positiveEigenvalue X i = some ℓ
  ordered : ∀ {g n : ℕ} (X : G.Moduli g n (fun _ => 0)) (i j : ℕ) (ℓ ν : ℝ),
    1 ≤ i → i ≤ j → positiveEigenvalue X i = some ℓ →
      positiveEigenvalue X j = some ν → ℓ ≤ ν
  measurable_le : ∀ (g n j : ℕ) (a : ℝ),
    MeasurableSet {X : G.Moduli g n (fun _ => 0) |
      ∃ ℓ, positiveEigenvalue X j = some ℓ ∧ ℓ ≤ a}
  measurable_lt : ∀ (g n j : ℕ) (a : ℝ),
    MeasurableSet {X : G.Moduli g n (fun _ => 0) |
      ∃ ℓ, positiveEigenvalue X j = some ℓ ∧ ℓ < a}
  many_pants : ∀ (g n : ℕ), Stable g n → ∀ (X : G.Moduli g n (fun _ => 0))
      (j : ℕ) (ε : ℝ), 1 ≤ j → 0 < ε → ε < 1 / 4 →
      j + 1 ≤ H.pantsCount X (ε / 6) →
      ∃ ℓ, positiveEigenvalue X j = some ℓ ∧ ℓ ≤ ε
  single_pant : ∃ c : ℝ, 0 < c ∧ ∀ (g n : ℕ), 2 ≤ g →
    ∀ (X : G.Moduli g n (fun _ => 0)) (L : ℝ), 0 < L → L ≤ 1 →
      c * L < 1 / 4 → 1 ≤ H.pantsCount X L →
      ∃ ℓ, positiveEigenvalue X 1 = some ℓ ∧ ℓ ≤ c * L

end WP.External
