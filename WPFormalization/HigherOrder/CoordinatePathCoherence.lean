import WPFormalization.HigherOrder.TriangularLocality
import WPFormalization.HigherOrder.Coherence
/-! The real adjacent-compatibility obligation for the prescribed canonical
hierarchy, and its purely algebraic implication for arbitrary finite paths.
CanonicalAdjacentCompatibility has no asserted inhabitant here and is not
an external input. The two helper theorems explicitly require its proof and do
not claim that the actual hierarchy already satisfies it at every order. -/
noncomputable section
namespace WP.HigherOrder
open Set

def CanonicalAdjacentCompatibility (P:PsiTheory) : Prop :=
  ∀Y∈Icc (0:ℝ) y₀,∀K:ℕ,0<K → ∀d:List ℕ,1≤d.length → ∀i:ℕ,i<d.length →
    profileCoefficient P Y (raiseDegree d i) K-profileCoefficient P Y d K=
      adjacentCoefficient P Y (formalHierarchyJet P Y) K i d

lemma canonical_coefficient_path_sum_of_adjacent (P:PsiTheory) (hcompat:CanonicalAdjacentCompatibility P)
    (p K:ℕ) (hp:1≤p) (hK:0<K) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀)
    (v:ℕ→List ℕ) (i:ℕ→ℕ) (n:ℕ)
    (hlen:∀s < n,(v s).length=p) (hi:∀s < n,i s<(v s).length)
    (hv:∀s < n,v (s+1)=raiseDegree (v s) (i s)) :
    (∑s∈Finset.range n,adjacentCoefficient P Y (formalHierarchyJet P Y) K (i s) (v s))=
      profileCoefficient P Y (v n) K-profileCoefficient P Y (v 0) K := by
  calc
    _=∑s∈Finset.range n,(profileCoefficient P Y (v (s+1)) K-profileCoefficient P Y (v s) K) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs':=Finset.mem_range.mp hs
      rw[hv s hs']
      exact (hcompat Y hY K hK (v s) (by rw[hlen s hs'];exact hp) (i s) (hi s hs')).symm
    _=_:=Finset.sum_range_sub (fun s=>profileCoefficient P Y (v s) K) n
lemma canonical_coefficient_path_independent_of_adjacent (P:PsiTheory) (hcompat:CanonicalAdjacentCompatibility P)
    (p K:ℕ) (hp:1≤p) (hK:0<K) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀)
    (v w:ℕ→List ℕ) (i j:ℕ→ℕ) (n m:ℕ)
    (hvlen:∀s < n,(v s).length=p) (hwlen:∀s < m,(w s).length=p)
    (hi:∀s < n,i s<(v s).length) (hj:∀s < m,j s<(w s).length)
    (hv:∀s < n,v (s+1)=raiseDegree (v s) (i s))
    (hw:∀s < m,w (s+1)=raiseDegree (w s) (j s))
    (hstart:v 0=w 0) (hend:v n=w m) :
    (∑s∈Finset.range n,adjacentCoefficient P Y (formalHierarchyJet P Y) K (i s) (v s))=
      ∑s∈Finset.range m,adjacentCoefficient P Y (formalHierarchyJet P Y) K (j s) (w s) := by
  rw[canonical_coefficient_path_sum_of_adjacent P hcompat p K hp hK Y hY v i n hvlen hi hv,
    canonical_coefficient_path_sum_of_adjacent P hcompat p K hp hK Y hY w j m hwlen hj hw,
    hstart,hend]
end WP.HigherOrder
