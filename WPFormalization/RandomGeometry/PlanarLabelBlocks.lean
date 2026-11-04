import Mathlib

/-! Ordered leaves carrying unordered, mutually disjoint cusp-label blocks. -/
noncomputable section
namespace WP.RandomGeometry
open Finset

/-- Each row is increasing. Only permutations within one leaf are removed;
the leaf/curve slots remain ordered. Empty rows and an empty leaf family are allowed. -/
def PlanarLabelBlocks (n r : ℕ) (k : Fin r → ℕ) :=
  {f : (Σ i : Fin r, Fin (k i)) ↪ Fin n //
    ∀ i, StrictMono (fun j : Fin (k i) => f ⟨i, j⟩)}

instance (n r : ℕ) (k : Fin r → ℕ) : Fintype (PlanarLabelBlocks n r k) :=
  inferInstanceAs (Fintype {f : (Σ i : Fin r, Fin (k i)) ↪ Fin n //
    ∀ i, StrictMono (fun j : Fin (k i) => f ⟨i, j⟩)})

/-- The genuinely unordered finite label blocks. -/
def UnorderedLabelBlocks (n r : ℕ) (k : Fin r → ℕ) :=
  {S : Fin r → Finset (Fin n) //
    (∀ i, (S i).card = k i) ∧ Pairwise (fun i j => Disjoint (S i) (S j))}

instance (n r : ℕ) (k : Fin r → ℕ) : Fintype (UnorderedLabelBlocks n r k) := by
  classical
  exact inferInstanceAs (Fintype {S : Fin r → Finset (Fin n) //
    (∀ i, (S i).card = k i) ∧ Pairwise (fun i j => Disjoint (S i) (S j))})

namespace UnorderedLabelBlocks
variable {n r : ℕ} {k : Fin r → ℕ}

def labelSet (S : UnorderedLabelBlocks n r k) (i : Fin r) : Finset (Fin n) := S.val i

lemma card (S : UnorderedLabelBlocks n r k) (i : Fin r) : (S.labelSet i).card = k i :=
  S.property.1 i

lemma disjoint (S : UnorderedLabelBlocks n r k) {i j : Fin r} (hij : i ≠ j) :
    Disjoint (S.labelSet i) (S.labelSet j) := S.property.2 hij

def enumeration (S : UnorderedLabelBlocks n r k) (i : Fin r) :
    Fin (k i) ≃o S.labelSet i := (S.labelSet i).orderIsoOfFin (S.card i)

def row (S : UnorderedLabelBlocks n r k) (i : Fin r) : Fin (k i) ↪ Fin n :=
  (S.enumeration i).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)

@[simp] lemma row_mem (S : UnorderedLabelBlocks n r k) (i : Fin r) (j : Fin (k i)) :
    S.row i j ∈ S.labelSet i := (S.enumeration i j).property

lemma row_strictMono (S : UnorderedLabelBlocks n r k) (i : Fin r) : StrictMono (S.row i) :=
  (S.enumeration i).strictMono

/-- The canonical increasing embedding of all the disjoint blocks. -/
def sorted (S : UnorderedLabelBlocks n r k) : PlanarLabelBlocks n r k := by
  let f : (Σ i : Fin r, Fin (k i)) → Fin n := fun p => S.row p.1 p.2
  have hf : Function.Injective f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ he
    by_cases hij : i = j
    · subst j
      have hab : a = b := (S.row i).injective he
      subst b
      rfl
    · have he' : S.row i a = S.row j b := he
      exact ((Finset.disjoint_left.mp (S.disjoint hij))
        (S.row_mem i a) (by rw [he']; exact S.row_mem j b)).elim
  exact ⟨⟨f, hf⟩, S.row_strictMono⟩

end UnorderedLabelBlocks

/-- Forget row ordering in an arbitrary full injective cusp tuple. -/
def blocksOfEmbedding {n r : ℕ} {k : Fin r → ℕ}
    (f : (Σ i : Fin r, Fin (k i)) ↪ Fin n) : UnorderedLabelBlocks n r k := by
  classical
  let S : Fin r → Finset (Fin n) := fun i => Finset.univ.image (fun j : Fin (k i) => f ⟨i, j⟩)
  refine ⟨S, ?_, ?_⟩
  · intro i
    rw [Finset.card_image_of_injective _ (fun a b h => eq_of_heq (Sigma.mk.inj_iff.mp (f.injective h)).2)]
    exact Fintype.card_fin (k i)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp hy
    exact hij (congrArg Sigma.fst (f.injective he.symm))

namespace PlanarLabelBlocks
variable {n r : ℕ} {k : Fin r → ℕ}

def labelSet (f : PlanarLabelBlocks n r k) (i : Fin r) : Finset (Fin n) :=
  (blocksOfEmbedding f.val).labelSet i

lemma labelSet_card (f : PlanarLabelBlocks n r k) (i : Fin r) :
    (f.labelSet i).card = k i := (blocksOfEmbedding f.val).card i

lemma labelSet_disjoint (f : PlanarLabelBlocks n r k) {i j : Fin r} (hij : i ≠ j) :
    Disjoint (f.labelSet i) (f.labelSet j) := (blocksOfEmbedding f.val).disjoint hij

@[simp] lemma mem_labelSet (f : PlanarLabelBlocks n r k) (i : Fin r) (x : Fin n) :
    x ∈ f.labelSet i ↔ ∃ j : Fin (k i), f.val ⟨i, j⟩ = x := by
  classical
  simp [labelSet, blocksOfEmbedding, UnorderedLabelBlocks.labelSet]

@[simp] lemma apply_mem_labelSet (f : PlanarLabelBlocks n r k) (i : Fin r) (j : Fin (k i)) :
    f.val ⟨i, j⟩ ∈ f.labelSet i := (f.mem_labelSet i _).mpr ⟨j, rfl⟩

end PlanarLabelBlocks

lemma blocksOfEmbedding_sorted {n r : ℕ} {k : Fin r → ℕ}
    (S : UnorderedLabelBlocks n r k) : blocksOfEmbedding S.sorted.val = S := by
  apply Subtype.ext
  funext i
  change Finset.univ.image (S.row i) = S.labelSet i
  exact Finset.image_orderEmbOfFin_univ _ _

lemma sorted_blocksOfEmbedding {n r : ℕ} {k : Fin r → ℕ}
    (f : PlanarLabelBlocks n r k) : (blocksOfEmbedding f.val).sorted = f := by
  apply Subtype.ext
  apply Function.Embedding.ext
  rintro ⟨i, j⟩
  have he := Finset.orderEmbOfFin_unique ((blocksOfEmbedding f.val).card i)
    (fun a : Fin (k i) => show f.val ⟨i, a⟩ ∈ (blocksOfEmbedding f.val).labelSet i from
      f.apply_mem_labelSet i a) (f.property i)
  exact (congrFun he j).symm

/-- Increasing rows are equivalent to actual unordered disjoint finite blocks. -/
def planarLabelBlocksEquivUnordered (n r : ℕ) (k : Fin r → ℕ) :
    PlanarLabelBlocks n r k ≃ UnorderedLabelBlocks n r k where
  toFun f := blocksOfEmbedding f.val
  invFun S := S.sorted
  left_inv := sorted_blocksOfEmbedding
  right_inv := blocksOfEmbedding_sorted

/-- Local row orderings are precisely the independent permutations within leaves. -/
def blockSlotPermutation {r : ℕ} {k : Fin r → ℕ}
    (σ : ∀ i, Equiv.Perm (Fin (k i))) : (Σ i : Fin r, Fin (k i)) ≃ (Σ i : Fin r, Fin (k i)) where
  toFun p := ⟨p.1, σ p.1 p.2⟩
  invFun p := ⟨p.1, (σ p.1).symm p.2⟩
  left_inv := by rintro ⟨i,j⟩; simp
  right_inv := by rintro ⟨i,j⟩; simp

def embeddingOfBlocks {n r : ℕ} {k : Fin r → ℕ}
    (S : UnorderedLabelBlocks n r k) (σ : ∀ i, Equiv.Perm (Fin (k i))) :
    (Σ i : Fin r, Fin (k i)) ↪ Fin n :=
  (blockSlotPermutation σ).toEmbedding.trans S.sorted.val

lemma blocksOf_embeddingOfBlocks {n r : ℕ} {k : Fin r → ℕ}
    (S : UnorderedLabelBlocks n r k) (σ : ∀ i, Equiv.Perm (Fin (k i))) :
    blocksOfEmbedding (embeddingOfBlocks S σ) = S := by
  classical
  apply Subtype.ext
  funext i
  change Finset.univ.image (fun j : Fin (k i) => S.row i (σ i j)) = S.labelSet i
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact S.row_mem i (σ i j)
  · intro hx
    let j := (S.enumeration i).symm ⟨x,hx⟩
    refine Finset.mem_image.mpr ⟨(σ i).symm j, Finset.mem_univ _, ?_⟩
    rw [(σ i).apply_symm_apply]
    exact congrArg Subtype.val ((S.enumeration i).apply_symm_apply ⟨x,hx⟩)

def embeddingRowEquiv {n r : ℕ} {k : Fin r → ℕ}
    (f : (Σ i : Fin r, Fin (k i)) ↪ Fin n) (i : Fin r) :
    Fin (k i) ≃ (blocksOfEmbedding f).labelSet i := by
  classical
  let e : Fin (k i) → (blocksOfEmbedding f).labelSet i := fun j =>
    ⟨f ⟨i,j⟩, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective e
  constructor
  · intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (f.injective (congrArg Subtype.val h))).2
  · intro x
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp x.property
    exact ⟨j, Subtype.ext hj⟩

def embeddingRowPermutation {n r : ℕ} {k : Fin r → ℕ}
    (f : (Σ i : Fin r, Fin (k i)) ↪ Fin n) (i : Fin r) : Equiv.Perm (Fin (k i)) :=
  (embeddingRowEquiv f i).trans ((blocksOfEmbedding f).enumeration i).toEquiv.symm

lemma embeddingRowPermutation_spec {n r : ℕ} {k : Fin r → ℕ}
    (f : (Σ i : Fin r, Fin (k i)) ↪ Fin n) (i : Fin r) (j : Fin (k i)) :
    (blocksOfEmbedding f).row i (embeddingRowPermutation f i j) = f ⟨i,j⟩ := by
  change (((blocksOfEmbedding f).enumeration i)
    (((blocksOfEmbedding f).enumeration i).symm (embeddingRowEquiv f i j)) : Fin n) = _
  exact congrArg Subtype.val (((blocksOfEmbedding f).enumeration i).apply_symm_apply _)

/-- Exact decomposition of a full injective tuple into actual unordered blocks
and independent within-block permutations; no permutation of the leaves occurs. -/
def embeddingBlockPermutationEquiv (n r : ℕ) (k : Fin r → ℕ) :
    ((Σ i : Fin r, Fin (k i)) ↪ Fin n) ≃
      UnorderedLabelBlocks n r k × (∀ i, Equiv.Perm (Fin (k i))) where
  toFun f := (blocksOfEmbedding f, embeddingRowPermutation f)
  invFun p := embeddingOfBlocks p.1 p.2
  left_inv f := by
    apply Function.Embedding.ext
    rintro ⟨i,j⟩
    exact embeddingRowPermutation_spec f i j
  right_inv p := by
    rcases p with ⟨S,σ⟩
    have hS := blocksOf_embeddingOfBlocks S σ
    apply Prod.ext hS
    funext i
    apply Equiv.ext
    intro j
    apply (S.row i).injective
    have h := embeddingRowPermutation_spec (embeddingOfBlocks S σ) i j
    rw [hS] at h
    exact h

/-- General ordered-leaf label count, valid also for zero-sized rows, no leaves,
and insufficient total cusp supply. -/
theorem planarLabelBlocks_card (n r : ℕ) (k : Fin r → ℕ) :
    Fintype.card (PlanarLabelBlocks n r k) * (∏ i, (k i).factorial) =
      n.descFactorial (∑ i, k i) := by
  have hc := Fintype.card_congr (embeddingBlockPermutationEquiv n r k)
  have hu := Fintype.card_congr (planarLabelBlocksEquivUnordered n r k)
  have h : Fintype.card (UnorderedLabelBlocks n r k) * (∏ i, (k i).factorial) =
      n.descFactorial (∑ i, k i) := by
    simpa only [Fintype.card_prod, Fintype.card_pi, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_embedding_eq, Fintype.card_sigma] using hc.symm
  rw [← hu] at h
  exact h

theorem planarLabelBlocks_nat_card (n r : ℕ) (k : Fin r → ℕ) :
    Nat.card (PlanarLabelBlocks n r k) * (∏ i, (k i).factorial) =
      n.descFactorial (∑ i, k i) := by
  simpa only [Nat.card_eq_fintype_card] using planarLabelBlocks_card n r k

namespace PlanarLabelBlocks
variable {n r : ℕ} {k : Fin r → ℕ}

theorem total_le (f : PlanarLabelBlocks n r k) : (∑ i, k i) ≤ n := by
  have h := Fintype.card_le_of_injective f.val f.val.injective
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

@[ext] theorem ext_labelSet (f q : PlanarLabelBlocks n r k)
    (h : ∀ i, f.labelSet i = q.labelSet i) : f = q := by
  apply (planarLabelBlocksEquivUnordered n r k).injective
  apply Subtype.ext
  funext i
  exact h i

theorem eq_of_row_cover (f q : PlanarLabelBlocks n r k)
    (h : ∀ i (j : Fin (k i)), ∃ a : Fin (k i), q.val ⟨i,a⟩ = f.val ⟨i,j⟩) :
    f = q := by
  apply f.ext_labelSet q
  intro i
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j,rfl⟩ := (f.mem_labelSet i x).mp hx
    exact (q.mem_labelSet i _).mpr (h i j)
  · rw [q.labelSet_card, f.labelSet_card]

theorem isEmpty_of_insufficient (h : n < ∑ i, k i) : IsEmpty (PlanarLabelBlocks n r k) :=
  ⟨fun f => (not_le_of_gt h) f.total_le⟩

end PlanarLabelBlocks

end WP.RandomGeometry
