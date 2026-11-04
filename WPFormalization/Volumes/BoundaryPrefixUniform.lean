import WPFormalization.Volumes.BoundaryPolynomial
import WPFormalization.Volumes.BoundaryUniformAssembly
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

def boundaryPrefixError (P:PsiTheory)(p:ℕ)(g q:ℕ)(L:Fin p→ℝ):ℝ :=
  boundaryVolumeModel P g (q+p) (Fin.append (fun _:Fin q=>0) L)/
    (volumeModel P g (q+p)*∏i,boundaryFactor (densityY (((q+p:ℕ):ℝ)/(g:ℝ))) (L i))-1

lemma bounded_boundary_prefix_estimate (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (N:ℕ)(ε:ℝ)(hε:0<ε) :
    ∃G:ℕ,∀g≥G,∀q≤N,∀L:Fin p→ℝ,(∀i,L i∈Icc 0 L₀)→
      |boundaryPrefixError P p g q L|≤ε := by
  obtain ⟨G,hG⟩:=bounded_cusp_count_boundary_estimate P (N+p) L₀ hL₀ ε hε
  refine ⟨G,?_⟩
  intro g hg q hq L hL
  have hlen : ∀ i:Fin (q+p), (Fin.append (fun _:Fin q=>0) L) i∈Icc 0 L₀ := by
    apply (Fin.forall_fin_add (m := q) (n := p) (fun i=>Fin.append (fun _:Fin q=>0) L i∈Icc 0 L₀)).mpr
    constructor
    · intro i
      simpa using (show (0:ℝ)∈Icc 0 L₀ from ⟨le_rfl,hL₀⟩)
    · intro i
      simpa using hL i
  have ht:=hG g hg (q+p) (by omega) (by omega)
    (Fin.append (fun _:Fin q=>0) L) (fun i=>(hlen i).1) (fun i=>(hlen i).2)
  unfold boundaryPrefixError
  simpa [Fin.prod_univ_add,boundaryFactor_zero_length] using ht

lemma boundary_prefix_uniform_of_sequential (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (hs:∀(gs qs:ℕ→ℕ)(Ls:ℕ→Fin p→ℝ),Tendsto gs atTop atTop→Tendsto qs atTop atTop→
      (∀j i,Ls j i∈Icc 0 L₀)→Tendsto (fun j=>boundaryPrefixError P p (gs j) (qs j) (Ls j)) atTop (𝓝 0)) :
    ∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀q:ℕ,∀L:Fin p→ℝ,(∀i,L i∈Icc 0 L₀)→
      |boundaryPrefixError P p g q L|≤ε := by
  apply uniform_of_bounded_counts_and_sequential (boundaryPrefixError P p) (fun L=>∀i,L i∈Icc 0 L₀)
  · exact fun N ε hε=>bounded_boundary_prefix_estimate P p hp L₀ hL₀ N ε hε
  · exact hs

end WP.BoundaryConvolution
