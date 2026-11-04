import WPFormalization.Volumes.CriticalCanonicalExpansion
/-! The proved critical extraction error is expressed directly at the original
densityY saddle parameter. The saddle identity is derived from its true
infimum-inverse specification, including the totalized k=0 definition. -/
noncomputable section
open Set
namespace WP.Analysis
lemma actual_critical_density_sector_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p) :
    ∃R C B c H:ℝ,0<R ∧ R<y₀ ∧ 0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      let Y:=densityY (2*(k:ℝ)/(complexity g p:ℝ))
      y₀-R<Y→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.extractedCoefficient P p j Y/(complexity g p:ℝ)^j|≤
      C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨R,C,B,c,H,hR,hRy,hC,hB,hc,hH,herror⟩:=actual_critical_extracted_expansion P p hp
  refine ⟨R,C,B,c,H,hR,hRy,hC,hB,hc,hH,?_⟩
  intro g k K hg hK
  dsimp only
  intro hlarge
  let h:ℝ:=complexity g p
  let Y:ℝ:=densityY (2*(k:ℝ)/h)
  have hh:0<h:=hH.trans_le hg
  have hd:=densityY_spec (2*(k:ℝ)/h) (by positivity)
  have hlarge':y₀-R<Y:=hlarge
  have hδ:y₀-Y∈Ioo (0:ℝ) R:=⟨sub_pos.mpr hd.1.2,by linarith⟩
  have hΨ:WP.Psi (XR Y)=(2*(k:ℝ)/h)/2 := by
    dsimp only[WP.Psi]
    rw[inverseY_eq_of_root _ _ hd.1.2.le rfl,hd.2]
  have hroot:(k:ℝ)=h*WP.Psi (XR Y):=by rw[hΨ];field_simp[hh.ne'] <;>ring
  have he:=herror g k K hg hK (y₀-Y) hδ (by simpa only[sub_sub_cancel] using hroot)
  simpa only[sub_sub_cancel] using he
end WP.Analysis
