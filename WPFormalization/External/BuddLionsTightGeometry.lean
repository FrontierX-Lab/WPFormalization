import WPFormalization.External.TightMulticurveTopology

/- Deterministic geometry from Budd--Lions arXiv:2506.02611v3:
Proposition 3.1 and Lemma 3.3 (pp.12--16), and the constructions inside the
proofs of Propositions 5.2--5.3 (pp.37--41), especially (60)--(61).
Only equal-length ties have an a.e. clause. Every extension is pointwise on an
arbitrary surface, arbitrary positive physical scale and marked ordered tuple;
the original coordinates are retained, so no tuple multiplicity is hidden.
The genus/face guard and epsilon below original interval endpoints are explicit.
The near-critical Boltzmann probability conclusions are not imported.
Phase two must construct/prove these geometric objects and deterministic facts. -/
noncomputable section
universe u v w z
namespace WP.External
open Set MeasureTheory
open scoped ENNReal

/- Pure pointwise geometry. The only measure statement is the classical
full-measure complement of equal-length simple-geodesic ties (BL Lemma 3.3).
The extension fields quantify an arbitrary fixed cusped surface, scale and
ordered tuple and retain the original tuple as a prefix: multiplicity is one. -/
@[blueprint "ext:tight-geometry"]
structure BuddLionsTightGeometry {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (T : TightRegions G) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q) where
  no_ties_ae : ∀ (g n : ℕ), 2 ≤ g →
    ∀ᵐ X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)
      ∂G.wpMeasure g (0+n) (Fin.append (fun _ => 0) (fun _ => 0)), Q.NoSimpleLengthTies (X:=X)
  /- A shortest tight curve is simple: the pointwise geometric fact used in
  Budd--Lions Proposition 5.3, proof p.40. This compares actual primitive curves,
  on a fixed surface and at an arbitrary physical cutoff; no measure appears. -/
  short_tight_has_simple : ∀ (g n : ℕ), 2 ≤ g →
    ∀ (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)) (b : ℝ),
    Q.NoSimpleLengthTies (X:=X) →
    (∃ γ : Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
      Q.primitive γ ∧ Q.IsTight γ ∧ Q.length γ ≤ b) →
    ∃ γ : Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
      Q.primitive γ ∧ Q.IsTight γ ∧ Q.simple γ ∧ Q.length γ ≤ b
  extend_no_short : ∀ (g n r : ℕ)
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)) (s ε B : ℝ),
    0 < s → 0 < ε → 0 < B → 2*B*((r:ℝ)+2)/ε+2 < g → Q.NoSimpleLengthTies (X:=X) →
    ∀ Γ : Fin r → Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
    Q.GoodTuple Γ → (∀ i, Q.length (Γ i) ≤ s*B) →
    (∀ γ : Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
      Q.primitive γ → Q.IsTight γ → Q.simple γ → s*ε < Q.length γ) →
    ((∃ γ : Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
        Q.primitive γ ∧ Q.IsTight γ ∧ Q.length γ ≤ s*B ∧ ¬ Q.simple γ) ∨
      ∃ γ δ : Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
        γ ≠ δ ∧ Q.primitive γ ∧ Q.primitive δ ∧ Q.IsTight γ ∧ Q.IsTight δ ∧
        Q.length γ ≤ s*B ∧ Q.length δ ≤ s*B ∧ ¬ Q.disjoint γ δ) →
    ∃ m : ℕ, (m:ℝ) ≤ 2*B*((r:ℝ)+2)/ε ∧
      ∃ Δ : Fin (r+m) → Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
        Q.GoodTuple Δ ∧ A.Separating Δ ∧
        (∀ i : Fin r, Δ (Fin.castAdd m i) = Γ i) ∧
        ∀ i, Q.length (Δ i) ≤ s*B*((r:ℝ)+2)
  augment_with_short : ∀ (g n r : ℕ)
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)) (s ε a B : ℝ),
    2 ≤ g → 0 < s → 0 < ε → ε < a → a ≤ B → Q.NoSimpleLengthTies (X:=X) →
    ∀ Γ : Fin r → Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
    Q.GoodTuple Γ → (∀ i, s*a ≤ Q.length (Γ i) ∧ Q.length (Γ i) ≤ s*B) →
    (∃ γ : Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
      Q.primitive γ ∧ Q.IsTight γ ∧ Q.simple γ ∧ Q.length γ ≤ s*ε) →
    ((∃ Δ : Fin (r+1) → Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
      Q.GoodTuple Δ ∧ (∀ i : Fin r, Δ (Fin.castAdd 1 i) = Γ i) ∧ Q.length (Δ (Fin.last r)) ≤ s*ε) ∨
    ∃ m : ℕ, m ≤ 3 ∧ ∃ Δ : Fin (r+m) → Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X,
      Q.GoodTuple Δ ∧ A.Separating Δ ∧ (∀ i : Fin r, Δ (Fin.castAdd m i) = Γ i) ∧
      ∀ i, Q.length (Δ i) ≤ s*(2*B+ε))

end WP.External
