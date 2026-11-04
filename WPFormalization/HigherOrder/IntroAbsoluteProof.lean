import WPFormalization.HigherOrder.IntroAbsoluteNumerical
import WPFormalization.Geometry.Bridge
/-! Exact geometric assembly of Theorem 1.1 from the numerical expansion.
The numerical Theorem 10.2 is proved from the registered classical external inputs.
This assembly transports it to any explicit WeilPeterssonGeometry realization;
it does not construct such a realization. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology
lemma intro_absolute_proof (P : PsiTheory) (G : External.WeilPeterssonGeometry P) :
    ∃ C B c : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ ∃ g₀ : ℕ, 0 < g₀ ∧
      (∀ (g : ℕ), g₀ ≤ g → ∀ (K : ℕ),
        (K : ℝ) ≤ c*Real.sqrt (2*(g : ℝ)-1) → ∀ n : ℕ,
        |External.cuspVolume G g n/leadingVolume g n -
          ∑ j ∈ Finset.range (K+1), absoluteCoefficient P j g n/(2*(g : ℝ)-1)^j| ≤
          C*B^(K+1)*((K+1).factorial : ℝ)^2/(2*(g : ℝ)-1)^(K+1)) ∧
      (∀ (g : ℕ), g₀ ≤ g → ∀ j n : ℕ,
        |absoluteCoefficient P j g n| ≤ C*B^j*(j.factorial : ℝ)^2) ∧
      (∃ C' : ℝ, 0 < C' ∧ ∀ (g : ℕ), g₀ ≤ g → ∀ n : ℕ,
        |External.cuspVolume G g n/leadingVolume g n-1| ≤ C'/(g : ℝ)) ∧
      (∃ c' a C' : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧
        ∀ (g : ℕ), g₀ ≤ g → ∀ n : ℕ,
          |External.cuspVolume G g n/leadingVolume g n -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (2*(g : ℝ)-1)⌋₊+1),
              absoluteCoefficient P j g n/(2*(g : ℝ)-1)^j| ≤
                C'*Real.exp (-a*Real.sqrt (2*(g : ℝ)-1))) := by
  obtain ⟨C,B,c,hC,hB,hc,N,hN,herr,hnorm,⟨D,hD,hfirst⟩,
    ⟨c',a,D',hc',hc'c,ha,hD',hopt⟩⟩:=intro_absolute_numerical_assembly P
  let N':ℕ:=max N 2
  refine ⟨C,B,c,hC,hB,hc,N',by dsimp[N'];omega,?_,?_,⟨D,hD,?_⟩,
    ⟨c',a,D',hc',hc'c,ha,hD',?_⟩⟩
  · intro g hg K hK n
    have hgN:N≤g:=(le_max_left _ _).trans hg
    have hg2:2≤g:=(le_max_right _ _).trans hg
    rw[Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)]
    exact herr g hgN K hK n
  · intro g hg j n
    exact hnorm g ((le_max_left _ _).trans hg) j n
  · intro g hg n
    have hgN:N≤g:=(le_max_left _ _).trans hg
    have hg2:2≤g:=(le_max_right _ _).trans hg
    rw[Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)]
    exact hfirst g hgN n
  · intro g hg n
    have hgN:N≤g:=(le_max_left _ _).trans hg
    have hg2:2≤g:=(le_max_right _ _).trans hg
    rw[Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)]
    exact hopt g hgN n
end WP.HigherOrder
