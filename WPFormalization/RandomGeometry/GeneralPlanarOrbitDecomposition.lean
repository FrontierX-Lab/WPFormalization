import WPFormalization.RandomGeometry.GeneralPlanarTuplePartition
import WPFormalization.RandomGeometry.GeneralPlanarStarIntegration

/-! Exact star/remainder decomposition of complete actual planar tuples. The
remainder is retained literally; no negligibility estimate is assumed. -/
set_option maxHeartbeats 0
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) {g n r : ℕ}

def generalPlanarTupleWindowSum (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (L : ℝ) (F : (Fin r → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑'γ : OrderedGeneralPlanarTuple (H:=H) X k L,F (fun i => H.length (γ.val i))

lemma generalPlanarOrbitShort_weighted_sum (o : GeneralPlanarOrbit T g n r k)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (F : (Fin r → ℝ) → ℝ≥0∞)
    (hsupport : ∀x,¬(∀i,x i≤L) →F x=0) :
    T.orbitSum o.val F X =
      ∑'γ : {γ : Fin r → H.Primitive g n X //
        T.orbitMem o.val X γ ∧∀i,H.length (γ i)≤L},
        F (fun i => H.length (γ.val i)) := by
  classical
  let p := fun γ : Fin r → H.Primitive g n X => T.orbitMem o.val X γ
  let q := fun γ : Fin r → H.Primitive g n X => ∀i,H.length (γ i)≤L
  let f := fun γ : Subtype p => F (fun i => H.length (γ.val i))
  have hs := tsum_subtype {γ : Subtype p | q γ.val} f
  let es : {γ : Subtype p | q γ.val} ≃ {γ : Subtype p // q γ.val} := Equiv.refl _
  have he := (es.trans (Equiv.subtypeSubtypeEquivSubtypeInter p q)).tsum_eq
    (fun γ => F (fun i => H.length (γ.val i)))
  calc
    _ = ∑'γ : Subtype p,({γ : Subtype p | q γ.val}).indicator f γ := by
      apply tsum_congr
      intro γ
      by_cases hq : q γ.val
      · simp only [Set.indicator,Set.mem_ofPred_eq,hq,ite_true];rfl
      · simpa only [Set.indicator,Set.mem_ofPred_eq,hq,ite_false] using hsupport _ hq
    _ = ∑'γ : {γ : Subtype p | q γ.val},f γ.val := hs.symm
    _ = _ := he

include C in
lemma generalPlanar_weighted_orbit_sum (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (F : (Fin r → ℝ) → ℝ≥0∞)
    (hsupport : ∀x,¬(∀i,x i≤L) →F x=0) :
    (∑'o : GeneralPlanarOrbit T g n r k,T.orbitSum o.val F X) =
      generalPlanarTupleWindowSum (H:=H) X k L F := by
  simp_rw [generalPlanarOrbitShort_weighted_sum T _ X L F hsupport]
  rw [←ENNReal.tsum_sigma]
  have he := (generalPlanarTuplePartitionEquiv T C hg X k L hL).tsum_eq
    (fun γ => F (fun i => H.length (γ.val i)))
  change (∑'p : GeneralPlanarShortTuple T X k L,F (fun i => H.length (p.2.val i))) = _
  convert he using 1
  · apply tsum_congr
    intro p
    rfl
  · rfl

/-- Actual nonstar orbit configurations. In particular, these have not been
silently identified with the nonnested star contribution. -/
def GeneralPlanarRemainderOrbit (g n r : ℕ) (k : Fin r → ℕ) :=
  {o : GeneralPlanarOrbit T g n r k //
    o ∉ Set.range (generalPlanarStarOrbitEmbedding T g n r k)}

instance (k : Fin r → ℕ) : Fintype (GeneralPlanarRemainderOrbit T g n r k) := by
  classical
  unfold GeneralPlanarRemainderOrbit
  infer_instance

def generalPlanarRemainderWindowSum (g n r : ℕ) (k : Fin r → ℕ)
    (F : (Fin r → ℝ) → ℝ≥0∞) (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑'o : GeneralPlanarRemainderOrbit T g n r k,T.orbitSum o.val.val F X

lemma embedding_tsum_decomposition {A B : Type*}
    (e : A ↪ B) (f : B → ℝ≥0∞) :
    (∑'b,f b)=(∑'a,f (e a)) + ∑'b : {b : B //b∉Set.range e},f b.val := by
  classical
  let S : Set B := Set.range e
  have hs := tsum_subtype S f
  have hc := tsum_subtype Sᶜ f
  have he := (Equiv.ofInjective e e.injective).tsum_eq (fun b : Set.range e => f b.val)
  calc
    _ = ∑'b : B,(S.indicator f b+Sᶜ.indicator f b) := by
      apply tsum_congr
      intro b
      by_cases hb : b∈S <;> simp [Set.indicator,hb]
    _ = (∑'b : B,S.indicator f b)+(∑'b : B,Sᶜ.indicator f b) := ENNReal.tsum_add
    _ = (∑'b : S,f b.val)+(∑'b : {b : B //b∉S},f b.val) := by rw [←hs,←hc];rfl
    _ = _ := congrArg (fun z => z+∑'b : {b : B //b∉S},f b.val) he.symm

lemma generalPlanarOrbit_sum_decomposition (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (F : (Fin r → ℝ) → ℝ≥0∞) :
    (∑'o : GeneralPlanarOrbit T g n r k,T.orbitSum o.val F X) =
      generalPlanarStarWindowSum T g n r k F X +
        generalPlanarRemainderWindowSum T g n r k F X := by
  classical
  let e := generalPlanarStarOrbitEmbedding T g n r k
  let f := fun o : GeneralPlanarOrbit T g n r k => T.orbitSum o.val F X
  change (∑'o : GeneralPlanarOrbit T g n r k,f o) =
    (∑'o : GeneralPlanarStarOrbit T g n r k,f (e o)) +
      ∑'o : {o : GeneralPlanarOrbit T g n r k //o∉Set.range e},f o.val
  exact embedding_tsum_decomposition e f

include C in
lemma generalPlanar_actual_star_remainder (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (F : (Fin r → ℝ) → ℝ≥0∞)
    (hsupport : ∀x,¬(∀i,x i≤L) →F x=0) :
    generalPlanarTupleWindowSum (H:=H) X k L F =
      generalPlanarStarWindowSum T g n r k F X +
        generalPlanarRemainderWindowSum T g n r k F X := by
  rw [←generalPlanar_weighted_orbit_sum T C hg X k L hL F hsupport]
  exact generalPlanarOrbit_sum_decomposition T X k F
end WP.RandomGeometry
