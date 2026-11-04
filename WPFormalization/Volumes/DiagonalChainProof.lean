import WPFormalization.Analysis.ChainUniformGluing
import WPFormalization.Statements.VolumeRatios
import WPFormalization.Volumes.DiagonalLargeGenus
import WPFormalization.Volumes.DiagonalFixedGenus

/-! Original Theorem 1.5, including every stable bounded-genus and planar
endpoint. Large genus uses the proved uniform cusp ratios; fixed genus
uses only the precisely isolated old Manin--Zograf input. -/
noncomputable section
namespace WP

theorem diagonal_chain_proof (P : PsiTheory) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g n : ℕ, Stable g n → N ≤ 2*g+n →
      |Real.log (normalizedVolume P g n) - ((2*(g : ℝ)+n)/2)*
        chainProfile ((n : ℝ)/(2*g+n))| ≤ ε*(2*g+n)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ G₀ : ℕ, ∀ G ≥ G₀, 2 ≤ G → ∀ j : ℕ, j ≤ G →
      |Real.log (volumeModel P (G-j) (2*j)/volumeModel P G 0)/G-
        chainProfile ((j : ℝ)/G)| ≤ ε) := by
  obtain ⟨C,hC,G,hV⟩ := volume_ratios P
  have hcusp : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n : ℝ)/g)-1| ≤ C/g :=
    ⟨C,hC,G,fun g hg n => ((hV g hg).1 n).2⟩
  have hlarge := diagonal_large_genus_of_cusp_ratios P hcusp
  have hfull := Analysis.chain_uniform_of_large_genus_and_fixed_genus
    (fun g n => Real.log (normalizedVolume P g n)-((2*(g : ℝ)+n)/2)*
      chainProfile ((n : ℝ)/(2*g+n)))
    (fun ε hε => by
      obtain ⟨G,hG⟩ := hlarge ε hε
      exact ⟨G,fun g hg n _ => hG g hg n⟩)
    (diagonal_fixed_genus_estimate P)
  exact ⟨hfull,diagonal_chain_quotient_of_full_estimate P hfull⟩

end WP
