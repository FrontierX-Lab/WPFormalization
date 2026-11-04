import WPFormalization.Volumes.BoundaryPrefixUniform
import WPFormalization.Marked.ExternalBoundaryPermutation
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma bounded_boundaries_of_prefix_uniform (P:PsiTheory)(p:ℕ)(L₀:ℝ)
    (hprefix:∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀q:ℕ,∀L:Fin p→ℝ,(∀i,L i∈Icc 0 L₀)→
      |boundaryPrefixError P p g q L|≤ε) :
    ∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀n:ℕ,p≤n→
      ∀L:Fin n→ℝ,(∀i,0≤L i)→(∀i,L i≤L₀)→
      (∀ i, p ≤ i.val → L i=0)→
      |boundaryVolumeModel P g n L/
        (volumeModel P g n*∏i,boundaryFactor (densityY ((n:ℝ)/g)) (L i))-1|≤ε := by
  classical
  intro ε hε
  obtain ⟨G,hG⟩:=hprefix ε hε
  refine ⟨G,?_⟩
  intro g hg n hn L hL0 hLU hzero
  obtain ⟨q,rfl⟩:=Nat.exists_eq_add_of_le hn
  let Lp:Fin p→ℝ:=fun i=>L (Fin.castAdd q i)
  have hLp:∀i,Lp i∈Icc 0 L₀:=fun i=>⟨hL0 _,hLU _⟩
  have hfun:L=Fin.append Lp (fun _:Fin q=>0):=by
    ext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp [Lp]
    · simpa using hzero (Fin.natAdd p j) (by simp)
  have ht:=hG g hg q Lp hLp
  have he:boundaryPrefixError P p g q Lp =
      boundaryVolumeModel P g (p+q) L/
        (volumeModel P g (p+q)*∏i,boundaryFactor (densityY (((p+q:ℕ):ℝ)/g)) (L i))-1:=by
    unfold boundaryPrefixError
    rw [boundaryVolumeModel_zero_prefix_eq_suffix]
    rw [hfun,Fin.prod_univ_add]
    simp [Nat.add_comm,boundaryFactor_zero_length]
  rw [he] at ht
  exact ht

end WP.BoundaryConvolution
