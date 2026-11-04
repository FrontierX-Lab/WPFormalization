import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.Basic

/-! Sparse cusp-label assignments, used to bound each fixed planar cut pattern.
The exponent is the actual number of nonroot cusp labels. -/
noncomputable section
namespace WP.RandomGeometry
open scoped BigOperators

def SparseCuspAssignment (n r a : ℕ) :=
  {f : Fin n → Fin (r+1) // (Finset.univ.filter (fun i => f i≠0)).card=a}

instance (n r a : ℕ) : Fintype (SparseCuspAssignment n r a) := by
  classical
  unfold SparseCuspAssignment
  infer_instance

def sparseCuspSupport {n r a : ℕ} (f : SparseCuspAssignment n r a) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f.val i≠0)

lemma sparseCuspSupport_card {n r a : ℕ} (f : SparseCuspAssignment n r a) :
    (sparseCuspSupport f).card=a := f.property

def sparseCuspSupportEquiv {n r a : ℕ} (f : SparseCuspAssignment n r a) :
    Fin a ≃ {i //i∈sparseCuspSupport f} :=
  (finCongr ((Fintype.card_coe (sparseCuspSupport f)).trans f.property).symm).trans
    (Fintype.equivFin _).symm

def sparseCuspEncoding {n r a : ℕ} (f : SparseCuspAssignment n r a) :
    (Fin a ↪ Fin n) × (Fin a → Fin (r+1)) :=
  (⟨fun j => (sparseCuspSupportEquiv f j).val,
    fun _ _ h => (sparseCuspSupportEquiv f).injective (Subtype.ext h)⟩,
    fun j => f.val (sparseCuspSupportEquiv f j).val)

lemma sparseCuspEncoding_injective {n r a : ℕ} :
    Function.Injective (sparseCuspEncoding : SparseCuspAssignment n r a → _) := by
  classical
  intro f g hfg
  have he : ∀j,(sparseCuspSupportEquiv f j).val=(sparseCuspSupportEquiv g j).val := by
    intro j
    exact congrFun (congrArg (fun x => (x.1 : Fin a ↪ Fin n).toFun) hfg) j
  have hv : ∀j,f.val (sparseCuspSupportEquiv f j).val=g.val (sparseCuspSupportEquiv g j).val := by
    intro j
    exact congrFun (congrArg Prod.snd hfg) j
  apply Subtype.ext
  funext i
  by_cases hfi : f.val i=0
  · by_cases hgi : g.val i=0
    · exact hfi.trans hgi.symm
    · have hm : i∈sparseCuspSupport g := by simp [sparseCuspSupport,hgi]
      obtain ⟨j,hj⟩ := (sparseCuspSupportEquiv g).surjective ⟨i,hm⟩
      have hji : (sparseCuspSupportEquiv g j).val=i := congrArg Subtype.val hj
      have hfj : (sparseCuspSupportEquiv f j).val=i := (he j).trans hji
      have hfm := (sparseCuspSupportEquiv f j).property
      rw [hfj] at hfm
      have hn : f.val i≠0 := by simpa [sparseCuspSupport] using hfm
      exact (hn hfi).elim
  · have hm : i∈sparseCuspSupport f := by simp [sparseCuspSupport,hfi]
    obtain ⟨j,hj⟩ := (sparseCuspSupportEquiv f).surjective ⟨i,hm⟩
    have hji : (sparseCuspSupportEquiv f j).val=i := congrArg Subtype.val hj
    have hgj : (sparseCuspSupportEquiv g j).val=i := (he j).symm.trans hji
    simpa only [hji,hgj] using hv j

lemma sparseCuspAssignment_card_le (n r a : ℕ) :
    Fintype.card (SparseCuspAssignment n r a)≤n^a*(r+1)^a := by
  classical
  calc
    _ ≤ Fintype.card ((Fin a ↪ Fin n) × (Fin a → Fin (r+1))) :=
      Fintype.card_le_of_injective sparseCuspEncoding sparseCuspEncoding_injective
    _ = n.descFactorial a*(r+1)^a := by simp [Fintype.card_embedding_eq]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow n a)
end WP.RandomGeometry
