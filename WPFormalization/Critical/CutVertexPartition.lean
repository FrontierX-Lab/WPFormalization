import WPFormalization.Critical.CutLocalCuspSeries

/-! A specified partition of the fixed graph vertices into the two unstable types and stable base complexities. The degree and Euler identities derive the total positive stable complexity H=2g-2+u. -/

noncomputable section
namespace WP.Critical
open Finset

/-- A specified vertex partition, with its three classes explicitly named.
Renaming the finite vertices has no geometric or asymptotic content. -/
structure CutVertexPartition (Q u v w:ℕ) where
  vertices : Fin Q≃(Fin u⊕(Fin v⊕Fin w))

namespace CutVertexPartition
variable {Q u v w:ℕ} (R:CutVertexPartition Q u v w)

def stableVertex (i:Fin w) : Fin Q := R.vertices.symm (Sum.inr (Sum.inr i))
def oneVertex (i:Fin u) : Fin Q := R.vertices.symm (Sum.inl i)
def twoVertex (i:Fin v) : Fin Q := R.vertices.symm (Sum.inr (Sum.inl i))

def genusVector (b:Fin w→ℕ) (c:Fin Q) : ℕ :=
  match R.vertices c with
  | Sum.inl _=>0
  | Sum.inr (Sum.inl _)=>0
  | Sum.inr (Sum.inr i)=>b i

include R in
lemma components_eq : Q=u+v+w := by
  have he := Fintype.card_congr R.vertices
  simpa only [Fintype.card_fin,Fintype.card_sum,Nat.add_assoc] using he

lemma genus_sum (b:Fin w→ℕ) : (∑c:Fin Q,R.genusVector b c)=(∑i:Fin w,b i) := by
  calc
    _ = ∑j:Fin u⊕(Fin v⊕Fin w),R.genusVector b (R.vertices.symm j) :=
      (Equiv.sum_comp R.vertices.symm (R.genusVector b)).symm
    _ = _ := by simp [genusVector,Fintype.sum_sum_type]

lemma cutLocalCuspSeries_eq_stable (a p:ℕ) (hs:Stable a p) :
    cutLocalCuspSeries a p=cutStableCuspSeries (complexity a p) := by
  have h01 : ¬(a=0 ∧ p=1) := by unfold Stable at hs;omega
  have h02 : ¬(a=0 ∧ p=2) := by unfold Stable at hs;omega
  simp only [cutLocalCuspSeries,h01,h02,ite_false]

lemma localSeries_product (p:Fin Q→ℕ) (b:Fin w→ℕ)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2)
    (hb:∀i,Stable (b i) (p (R.stableVertex i))) :
    (∏c:Fin Q,cutLocalCuspSeries (R.genusVector b c) (p c))=
      cutCuspAllocationSeries u v*
        (∏i:Fin w,cutStableCuspSeries (complexity (b i) (p (R.stableVertex i)))) := by
  have he : (∏c:Fin Q,cutLocalCuspSeries (R.genusVector b c) (p c))=
      ∏j:Fin u⊕(Fin v⊕Fin w),
        cutLocalCuspSeries (R.genusVector b (R.vertices.symm j)) (p (R.vertices.symm j)) :=
    (Equiv.prod_comp R.vertices.symm _).symm
  rw [he,Fintype.prod_sum_type,Fintype.prod_sum_type]
  have h1 : (∏i:Fin u,cutLocalCuspSeries (R.genusVector b (R.vertices.symm (Sum.inl i)))
      (p (R.vertices.symm (Sum.inl i))))=cutPhi01^u := by
    have he (i:Fin u) : p (R.vertices.symm (Sum.inl i))=1 := h01 i
    simp [genusVector,he,cutLocalCuspSeries]
  have h2 : (∏i:Fin v,cutLocalCuspSeries (R.genusVector b (R.vertices.symm (Sum.inr (Sum.inl i))))
      (p (R.vertices.symm (Sum.inr (Sum.inl i)))))=cutPhi02^v := by
    have he (i:Fin v) : p (R.vertices.symm (Sum.inr (Sum.inl i)))=2 := h02 i
    simp [genusVector,he,cutLocalCuspSeries]
  rw [h1,h2]
  unfold cutCuspAllocationSeries
  rw [mul_assoc]
  congr 1
  congr 1
  apply prod_congr rfl
  intro i hi
  change cutLocalCuspSeries (R.genusVector b (R.vertices.symm (Sum.inr (Sum.inr i))))
    (p (R.stableVertex i))=_
  simp only [genusVector,R.vertices.apply_symm_apply]
  exact cutLocalCuspSeries_eq_stable _ _ (hb i)

end CutVertexPartition
end WP.Critical
namespace WP.Critical
namespace CutVertexPartition
open Finset
variable {Q u v w:ℕ} (R:CutVertexPartition Q u v w)

lemma degrees_sum (p:Fin Q→ℕ)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2) :
    (∑c:Fin Q,p c)=u+2*v+(∑i:Fin w,p (R.stableVertex i)) := by
  calc
    _ = ∑j:Fin u⊕(Fin v⊕Fin w),p (R.vertices.symm j) :=
      (Equiv.sum_comp R.vertices.symm p).symm
    _ = _ := by
      have h1 (i:Fin u):p (R.vertices.symm (Sum.inl i))=1 := h01 i
      have h2 (i:Fin v):p (R.vertices.symm (Sum.inr (Sum.inl i)))=2 := h02 i
      simp only [Fintype.sum_sum_type,h1,h2,sum_const,card_univ,Fintype.card_fin,
        smul_eq_mul,mul_one,stableVertex]
      omega

/-- The stable positive complexities have total H=2g-2+u, as derived from
actual graph Euler and degree budgets rather than supplied as an estimate. -/
lemma stableComplexity_budget (g k:ℕ) (hg:w+2≤g) (p:Fin Q→ℕ) (b:Fin w→ℕ)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2)
    (hb:∀i,Stable (b i) (p (R.stableVertex i)))
    (hp:(∑c:Fin Q,p c)=2*k)
    (heuler:(∑c:Fin Q,R.genusVector b c)+k+1=g+Q) :
    (∑i:Fin w,complexity (b i) (p (R.stableVertex i)))=(2*g-2+u-w)+w := by
  have hlocal (i:Fin w) : complexity (b i) (p (R.stableVertex i))+2=
      2*b i+p (R.stableVertex i) := by
    have hs:=hb i
    unfold Stable complexity at *
    omega
  have hs := congrArg (fun f:Fin w→ℕ=>∑i,f i) (funext hlocal)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,←mul_sum] at hs
  have hQ := R.components_eq
  have hP := R.degrees_sum p h01 h02
  have hG := R.genus_sum b
  rw [hG] at heuler
  omega

end CutVertexPartition
end WP.Critical
