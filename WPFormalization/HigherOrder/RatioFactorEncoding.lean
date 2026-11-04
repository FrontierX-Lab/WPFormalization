import WPFormalization.HigherOrder.ActualRatioProduct
import WPFormalization.HigherOrder.TriangularLocality
/-! A finite factor array encodes exactly the actual C.14 core and its
canonical formal counterpart, with an optional actual/formal profile factor.
Both product identities are proved by finite reindexing, not by matching an
assumed asymptotic series or evaluating the infinite formal hierarchy. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def actualLargeRatioFactor (P:PsiTheory)(g p j s:ℕ)(Y:ℝ)(i:ℕ):ℝ :=
  if i<2*j+s then cuspCorrection P (g-j) (p-s+i) Y/
    (1-(((2*j+s-i:ℕ):ℝ)/(complexity g p:ℝ)))
  else genusCorrection P (g-(i-(2*j+s))) (p+2*(i-(2*j+s))) Y

def formalLargeRatioFactor (F:HierarchyJet)(p j s i:ℕ):Series :=
  if i<2*j+s then complexityShift (((2*j+s:ℕ):ℝ)-i) (F.cusp (p-s+i))*
    (1-PowerSeries.C ((2*j+s-i:ℕ):ℝ)*PowerSeries.X)⁻¹
  else F.genus (p+2*(i-(2*j+s)))

lemma actualLargeRatioFactor_product (P:PsiTheory)(g p j s:ℕ)(Y:ℝ) :
    (∏i∈Finset.range ((2*j+s)+j),actualLargeRatioFactor P g p j s Y i)=
      actualLargeRatioCore P g p j s Y := by
  rw [Finset.prod_range_add]
  unfold actualLargeRatioCore
  apply congrArg₂ (fun a b:ℝ=>a*b)
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [actualLargeRatioFactor,if_pos (Finset.mem_range.mp hi)]
  · apply Finset.prod_congr rfl
    intro b hb
    simp only [actualLargeRatioFactor,if_neg (by omega : ¬((2*j+s)+b<2*j+s)),Nat.add_sub_cancel_left]

lemma formalLargeRatioFactor_product (F:HierarchyJet)(p j s:ℕ) :
    (∏i∈Finset.range ((2*j+s)+j),formalLargeRatioFactor F p j s i)=
      ratioCoreSeries F p j s := by
  rw [Finset.prod_range_add]
  dsimp only [ratioCoreSeries]
  apply congrArg₂ (fun a b:Series=>a*b)
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [formalLargeRatioFactor,if_pos (Finset.mem_range.mp hi)]
  · apply Finset.prod_congr rfl
    intro b hb
    simp only [formalLargeRatioFactor,if_neg (by omega : ¬((2*j+s)+b<2*j+s)),Nat.add_sub_cancel_left]

lemma product_append_one {R:Type*}[CommMonoid R](f:ℕ→R)(x:R)(n:ℕ) :
    (∏i∈Finset.range (n+1),if i<n then f i else x)=(∏i∈Finset.range n,f i)*x := by
  rw [Finset.prod_range_succ,if_neg (by omega : ¬n<n)]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [if_pos (Finset.mem_range.mp hi)]

def actualRatioProfileFactor (P:PsiTheory)(g p j s:ℕ)(Y x:ℝ)(i:ℕ):ℝ :=
  if i<(2*j+s)+j then actualLargeRatioFactor P g p j s Y i else x

def formalRatioProfileFactor (F:HierarchyJet)(p j s:ℕ)(u:Series)(i:ℕ):Series :=
  if i<(2*j+s)+j then formalLargeRatioFactor F p j s i else u

lemma actualRatioProfileFactor_product (P:PsiTheory)(g p j s:ℕ)(Y x:ℝ) :
    (∏i∈Finset.range ((2*j+s)+j+1),actualRatioProfileFactor P g p j s Y x i)=
      actualLargeRatioCore P g p j s Y*x := by
  unfold actualRatioProfileFactor
  rw [product_append_one,actualLargeRatioFactor_product]

lemma formalRatioProfileFactor_product (F:HierarchyJet)(p j s:ℕ)(u:Series) :
    (∏i∈Finset.range ((2*j+s)+j+1),formalRatioProfileFactor F p j s u i)=
      ratioCoreSeries F p j s*u := by
  unfold formalRatioProfileFactor
  rw [product_append_one,formalLargeRatioFactor_product]

end WP.HigherOrder
