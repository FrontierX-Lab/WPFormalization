import WPFormalization.Tight.SpectrumTupleExtensionsPointProcess
/- Exact finite-block embedding count for genuine primitive tight spectrum
window counts. No probability or moment estimate occurs in the input. -/
import WPFormalization.Tight.SpectrumTupleExtensionsOrbitSum
import Mathlib.Data.Fintype.CardEmbedding
noncomputable section
universe u v w z
namespace WP.Tight
open Set
open scoped ENNReal NNReal

def injectiveTupleEquivEmbedding (α : Type w) (r : ℕ) :
    {f : Fin r → α // Function.Injective f} ≃ (Fin r ↪ α) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f, f.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_injective_tuple_eq_descFactorial (α : Type w) [Finite α] (r : ℕ) :
    Nat.card {f : Fin r → α // Function.Injective f} = (Nat.card α).descFactorial r := by
  classical
  letI := Fintype.ofFinite α
  rw [Nat.card_congr (injectiveTupleEquivEmbedding α r), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin, Nat.card_eq_fintype_card]

def blockTupleEquivProductEmbeddings {α : Type w} {d : ℕ}
    (S : Fin d → Set α) (m : Fin d → ℕ) (hdisj : Pairwise fun i j => Disjoint (S i) (S j)) :
    {f : (Σ i : Fin d, Fin (m i)) → α //
      Function.Injective f ∧ ∀ a, f a ∈ S a.1} ≃
      ((i : Fin d) → (Fin (m i) ↪ ↥(S i))) where
  toFun f i := ⟨fun j => ⟨f.val ⟨i,j⟩, f.property.2 ⟨i,j⟩⟩, by
    intro j k heq
    have h := f.property.1 (congrArg Subtype.val heq)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
  invFun f := ⟨fun a => (f a.1 a.2).val, by
    refine ⟨?_, ?_⟩
    · intro a b heq
      rcases a with ⟨i,j⟩
      rcases b with ⟨k,l⟩
      have hik : i = k := by
        by_contra hne
        have hnone := Set.disjoint_left.mp (hdisj hne)
        have heq' : (f i j).val = (f k l).val := heq
        have hm : (f i j).val ∈ S k := by
          rw [heq']
          exact (f k l).property
        exact hnone (f i j).property hm
      subst k
      have hjl := (f i).injective (Subtype.ext heq)
      cases hjl
      rfl
    · intro a
      exact (f a.1 a.2).property⟩
  left_inv f := rfl
  right_inv f := by
    funext i
    apply Function.Embedding.ext
    intro j
    rfl

lemma block_tuple_card_eq_product_descFactorial {α : Type w} {d : ℕ}
    (S : Fin d → Set α) (m : Fin d → ℕ) (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    [∀ i, Finite (S i)] :
    Nat.card {f : (Σ i : Fin d, Fin (m i)) → α //
      Function.Injective f ∧ ∀ a, f a ∈ S a.1} =
      ∏ i : Fin d, (Nat.card (S i)).descFactorial (m i) := by
  classical
  rw [Nat.card_congr (blockTupleEquivProductEmbeddings S m hdisj), Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i hi
  letI := Fintype.ofFinite (S i)
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    Nat.card_eq_fintype_card]

def blockIndexEquiv {d : ℕ} (m : Fin d → ℕ) :
    (Σ i : Fin d, Fin (m i)) ≃ Fin (∑ i, m i) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

lemma tight_primitive_window_finite {P : PsiTheory}
    {G : External.WeilPeterssonGeometry.{u,v} P} {T : External.TightRegions G}
    {H : External.HyperbolicCurveGeometry.{u,v,w} G}
    (Q : External.TightGeodesicGeometry G T H) {g n : ℕ}
    (X : External.TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (s : ℝ) (hs : 0<s) (W : WP.Probability.RelCompactBorelWindow ℝ≥0) :
    Finite {γ : H.Primitive g n (External.tightCuspSurface G X) //
      Q.cuspTight X γ ∧ Real.toNNReal (s*H.length γ) ∈ W.carrier} := by
  letI := RandomGeometry.curveNNLengthMeasure_finite_window H (External.tightCuspSurface G X)
    s hs (Q.cuspTight X) W.carrier (W.compactClosure.bddAbove.mono subset_closure)
  apply Finite.of_injective (fun γ : {γ : H.Primitive g n (External.tightCuspSurface G X) //
      Q.cuspTight X γ ∧ Real.toNNReal (s*H.length γ) ∈ W.carrier} =>
    (⟨⟨γ.val,γ.property.1⟩,γ.property.2⟩ :
      {γ : {γ : H.Primitive g n (External.tightCuspSurface G X) // Q.cuspTight X γ} //
        Real.toNNReal (s*H.length γ.val) ∈ W.carrier}))
  intro a b h
  exact Subtype.ext (congrArg (fun γ=>γ.val.val) h)

lemma block_tight_tuple_card_eq_mixed_factorial {P : PsiTheory}
    {G : External.WeilPeterssonGeometry.{u,v} P} {T : External.TightRegions G}
    {H : External.HyperbolicCurveGeometry.{u,v,w} G}
    (Q : External.TightGeodesicGeometry G T H) {g n d : ℕ}
    (X : External.TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (s : ℝ) (hs : 0<s) (W : Fin d → WP.Probability.RelCompactBorelWindow ℝ≥0)
    (hdisj : WP.Probability.DisjointWindows ℝ≥0 W) (m : Fin d → ℕ) :
    Nat.card {Γ : (Σ i : Fin d, Fin (m i)) → H.Primitive g n (External.tightCuspSurface G X) //
      Function.Injective Γ ∧ ∀ a, Q.cuspTight X (Γ a) ∧
        Real.toNNReal (s*H.length (Γ a)) ∈ (W a.1).carrier} =
      ∏ i : Fin d, ((tightLengthPointMeasure Q X s hs).count ℝ≥0 (W i)).descFactorial (m i) := by
  let S : Fin d → Set (H.Primitive g n (External.tightCuspSurface G X)) := fun i=>
    {γ | Q.cuspTight X γ ∧ Real.toNNReal (s*H.length γ) ∈ (W i).carrier}
  have hfinite : ∀ i, Finite (S i) := fun i=>tight_primitive_window_finite Q X s hs (W i)
  letI := hfinite
  have hd : Pairwise fun i j=>Disjoint (S i) (S j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro γ hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.2 hj.2
  have hc := block_tuple_card_eq_product_descFactorial S m hd
  change Nat.card {Γ : (Σ i : Fin d, Fin (m i)) → H.Primitive g n (External.tightCuspSurface G X) //
    Function.Injective Γ ∧ ∀ a, Γ a ∈ S a.1} = _
  rw [hc]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  exact (tightLengthPointMeasure_window_count Q X s hs (W i)).symm

def blockTupleReindexEquiv {α : Type w} {d : ℕ} (S : Fin d→Set α) (m : Fin d→ℕ) :
    {f : (Σi : Fin d,Fin (m i))→α // Function.Injective f ∧ ∀a,f a∈S a.1} ≃
    {f : Fin (∑i,m i)→α // Function.Injective f ∧
      ∀j,f j∈S ((blockIndexEquiv m).symm j).1} where
  toFun f := ⟨fun j=>f.val ((blockIndexEquiv m).symm j),by
    refine ⟨?_,fun j=>f.property.2 _⟩
    intro a b h
    exact (blockIndexEquiv m).symm.injective (f.property.1 h)⟩
  invFun f := ⟨fun a=>f.val (blockIndexEquiv m a),by
    refine ⟨?_,?_⟩
    · intro a b h
      exact (blockIndexEquiv m).injective (f.property.1 h)
    · intro a
      simpa only [Equiv.symm_apply_apply] using f.property.2 (blockIndexEquiv m a)⟩
  left_inv f := by apply Subtype.ext;funext a;simp
  right_inv f := by apply Subtype.ext;funext j;simp

lemma flat_tight_tuple_card_eq_mixed_factorial {P : PsiTheory}
    {G : External.WeilPeterssonGeometry.{u,v} P} {T : External.TightRegions G}
    {H : External.HyperbolicCurveGeometry.{u,v,w} G}
    (Q : External.TightGeodesicGeometry G T H) {g n d : ℕ}
    (X : External.TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (s : ℝ) (hs : 0<s) (W : Fin d→WP.Probability.RelCompactBorelWindow ℝ≥0)
    (hd : WP.Probability.DisjointWindows ℝ≥0 W) (m : Fin d→ℕ) :
    Nat.card {Γ : Fin (∑i,m i)→H.Primitive g n (External.tightCuspSurface G X) //
      Function.Injective Γ ∧ ∀j,Q.cuspTight X (Γ j) ∧
        Real.toNNReal (s*H.length (Γ j))∈(W ((blockIndexEquiv m).symm j).1).carrier} =
      ∏i : Fin d,((tightLengthPointMeasure Q X s hs).count ℝ≥0 (W i)).descFactorial (m i) := by
  exact (Nat.card_congr (blockTupleReindexEquiv
    (fun i=>{γ : H.Primitive g n (External.tightCuspSurface G X) |
      Q.cuspTight X γ ∧ Real.toNNReal (s*H.length γ)∈(W i).carrier}) m)).symm.trans
    (block_tight_tuple_card_eq_mixed_factorial Q X s hs W hd m)

def flattenedPhysicalWindows {d : ℕ} (s : ℝ)
    (W : Fin d→WP.Probability.RelCompactBorelWindow ℝ≥0) (m : Fin d→ℕ) :
    Fin (∑i,m i)→Set ℝ := fun j=>
  {l | Real.toNNReal (s*l)∈(W ((blockIndexEquiv m).symm j).1).carrier}

lemma flattenedPhysicalWindows_bounded {d : ℕ} (s : ℝ) (hs : 0<s)
    (W : Fin d→WP.Probability.RelCompactBorelWindow ℝ≥0) (m : Fin d→ℕ)
    (B : ℝ≥0) (hW : ∀i,(W i).carrier⊆Iic B) :
    ∀ j,∀l∈flattenedPhysicalWindows s W m j,l≤(B:ℝ)/s := by
  intro j l hl
  have hh : Real.toNNReal (s*l)≤B := hW _ hl
  have hreal : s*l≤(B:ℝ) :=
    (Real.le_coe_toNNReal (s*l)).trans (by exact_mod_cast hh)
  apply (le_div_iff₀ hs).mpr
  simpa only [mul_comm] using hreal

lemma product_flattened_repetitions {α : Type w} [CommMonoid α] {d : ℕ}
    (m : Fin d→ℕ) (a : Fin d→α) :
    (∏j : Fin (∑i,m i),a ((blockIndexEquiv m).symm j).1) = ∏i : Fin d,a i^(m i) := by
  rw [←(blockIndexEquiv m).prod_comp]
  simp only [Equiv.symm_apply_apply,Fintype.prod_sigma,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end WP.Tight
