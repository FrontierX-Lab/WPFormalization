import WPFormalization.External.TightMoments
import WPFormalization.External.HyperbolicCurveGeometry

/- Classical geometric objects for the tight length spectrum.
Budd--Lions, arXiv:2506.02611v3, Section 3 (pp.12--17) and Section 5 (pp.37--41).
All unoriented closed geodesics are retained, with separate primitive/simple
predicates and the SAME capped homotopy classes as T.cycles. On all-cusp
surfaces their primitive subtype is identified with the actual H.Primitive.
The tight count has no simplicity condition. Construction of these geometric
objects, with the specified meaning, remains an explicit phase-two obligation.
No new-paper estimate or concrete-instance existence is asserted. -/
noncomputable section
universe u v w z
namespace WP.External
open Set MeasureTheory
open scoped ENNReal

abbrev TightSurface {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (g p k : ℕ) (L : Fin p → ℝ) (K : Fin k → ℝ) :=
  G.Moduli g (p+k) (Fin.append L K)

lemma append_zero_lengths (p k : ℕ) :
    Fin.append (fun _ : Fin p => (0 : ℝ)) (fun _ : Fin k => (0 : ℝ)) =
      fun _ : Fin (p+k) => (0 : ℝ) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

def tightCuspSurface {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    {g n : ℕ} (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)) :
    G.Moduli g n (fun _ => 0) := by
  have X0 : G.Moduli g (0+n) (fun _ => 0) := by
    simpa only [TightSurface, append_zero_lengths] using X
  exact (Nat.zero_add n) ▸ X0

/- All unoriented closed geodesics are retained. Primitive/simple are separate
predicates; in particular the primitive tight spectrum is not replaced by its
simple part. The cap map lands in the SAME filled classes as protected cycles. -/
structure TightGeodesicGeometry {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (T : TightRegions G) (H : HyperbolicCurveGeometry.{u,v,w} G) where
  Geodesic : ∀ (g p k : ℕ) (L : Fin p → ℝ) (K : Fin k → ℝ),
    TightSurface G g p k L K → Type w
  length : ∀ {g p k L K X}, Geodesic g p k L K X → ℝ
  length_pos : ∀ {g p k L K X} (γ : Geodesic g p k L K X), 0 < length γ
  primitive : ∀ {g p k L K X}, Geodesic g p k L K X → Prop
  simple : ∀ {g p k L K X}, Geodesic g p k L K X → Prop
  simple_primitive : ∀ {g p k L K X} (γ : Geodesic g p k L K X), simple γ → primitive γ
  disjoint : ∀ {g p k L K X}, Geodesic g p k L K X → Geodesic g p k L K X → Prop
  simpleCycle : ∀ {g p k L K X} (γ : Geodesic g p k L K X), simple γ →
    T.cycles.SimpleCycle g (p+k) (Fin.append L K) X
  cap : ∀ {g p k L K X}, Geodesic g p k L K X → T.cycles.CappedClass g p k L K X
  simpleCycle_length : ∀ {g p k L K X} (γ : Geodesic g p k L K X) (hγ : simple γ),
    T.cycles.length _ _ _ _ (simpleCycle γ hγ) = length γ
  simpleCycle_cap : ∀ {g p k L K X} (γ : Geodesic g p k L K X) (hγ : simple γ),
    T.cycles.cap g p k L K X (simpleCycle γ hγ) = cap γ
  simpleCycle_injective : ∀ {g p k L K X} (γ δ : Geodesic g p k L K X)
    (hγ : simple γ) (hδ : simple δ), simpleCycle γ hγ = simpleCycle δ hδ → γ = δ
  shortPrimitive : ∀ {g p k L K} (X : TightSurface G g p k L K) (b : ℝ),
    Finset {γ : Geodesic g p k L K X // primitive γ}
  mem_shortPrimitive : ∀ {g p k L K} (X : TightSurface G g p k L K) (b : ℝ)
    (γ : {γ : Geodesic g p k L K X // primitive γ}),
    γ ∈ shortPrimitive X b ↔ length γ.val ≤ b
  cuspPrimitiveEquiv : ∀ (g n : ℕ)
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0)),
    {γ : Geodesic g 0 n (fun _ => 0) (fun _ => 0) X // primitive γ} ≃
      H.Primitive g n (tightCuspSurface G X)
  cuspPrimitive_length : ∀ (g n : ℕ)
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))
    (γ : {γ : Geodesic g 0 n (fun _ => 0) (fun _ => 0) X // primitive γ}),
    H.length (cuspPrimitiveEquiv g n X γ) = length γ.val
  cuspPrimitive_simple : ∀ (g n : ℕ)
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))
    (γ : {γ : Geodesic g 0 n (fun _ => 0) (fun _ => 0) X // primitive γ}),
    H.simple (cuspPrimitiveEquiv g n X γ) ↔ simple γ.val

namespace TightGeodesicGeometry
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P} {T : TightRegions G}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (Q : TightGeodesicGeometry G T H)

def IsTight {g p k L K X} (γ : Q.Geodesic g p k L K X) : Prop :=
  Q.cap γ ≠ T.cycles.nullClass g p k L K X ∧
  ∀ δ : Q.Geodesic g p k L K X, Q.cap δ = Q.cap γ → Q.length δ ≤ Q.length γ → δ = γ

def IsProper {g p k L K X} (γ : Q.Geodesic g p k L K X) : Prop :=
  Q.cap γ ≠ T.cycles.nullClass g p k L K X ∧
  ∀ i : Fin p, Q.cap γ ≠ T.cycles.cap g p k L K X
    (T.cycles.boundary g (p+k) (Fin.append L K) X (Fin.castAdd k i))

def GoodTuple {g p k L K X r} (γ : Fin r → Q.Geodesic g p k L K X) : Prop :=
  Function.Injective γ ∧
  (∀ i, Q.primitive (γ i) ∧ Q.IsTight (γ i) ∧ Q.simple (γ i) ∧ Q.IsProper (γ i)) ∧
  ∀ i j, i ≠ j → Q.disjoint (γ i) (γ j)

def NoSimpleLengthTies {g p k : ℕ} {L : Fin p → ℝ} {K : Fin k → ℝ}
    {X : TightSurface G g p k L K} : Prop :=
  ∀ γ δ : Q.Geodesic g p k L K X,
    Q.simple γ → Q.simple δ → Q.IsProper γ → Q.IsProper δ →
    Q.length γ = Q.length δ → γ = δ


/- The full primitive tight count is a subtype of the SAME actual H.Primitive.
No simplicity predicate occurs in this definition. -/
def cuspTight {g n : ℕ} (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))
    (γ : H.Primitive g n (tightCuspSurface G X)) : Prop :=
  Q.IsTight (((Q.cuspPrimitiveEquiv g n X).symm γ).val)

def cuspTightCount {g n : ℕ} (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))
    (I : Set ℝ) : ℕ :=
  Nat.card {γ : H.Primitive g n (tightCuspSurface G X) // Q.cuspTight X γ ∧ H.length γ ∈ I}

end TightGeodesicGeometry

end WP.External
