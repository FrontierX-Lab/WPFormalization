import WPFormalization.Volumes.GrowingBoundaryKimura

/-! Original equation (7.19) and the complete boundary-length consequence
advertised in the introduction. This public statement is separated from the
moment estimates and asymptotic proof implementation. -/
noncomputable section
universe u v
namespace WP
open Filter
open scoped Topology

/- Full fixed-cusp boundary conclusion: the all-length quadratic relative
error, the growing-length boundary-factor limit, and the Kimura Gamma
normalization. S(0)=1 is explicit. The geometric input is the existing
classical WP/intersection dictionary; there is no new boundary asymptotic
or Kimura conjecture premise. -/
@[blueprint "eq:boundary-factor"]
theorem growing_boundary_factor (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P) (n : ℕ) (hn : 1 ≤ n) :
    (∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ L : Fin n → ℝ,
      (∀ i, 0 ≤ L i) →
      0 ≤ 1-External.wpVolume G g n L /
        (External.cuspVolume G g n *
          ∏ i, (if L i=0 then 1 else Real.sinh (L i/2)/(L i/2))) ∧
      1-External.wpVolume G g n L /
        (External.cuspVolume G g n *
          ∏ i, (if L i=0 then 1 else Real.sinh (L i/2)/(L i/2))) ≤
        C/g * ∑ i, (L i)^2) ∧
    (∀ L : ℕ → Fin n → ℝ, (∀ g i, 0 ≤ L g i) →
      (∀ i, Tendsto (fun g : ℕ => L g i/Real.sqrt g) atTop (𝓝 0)) →
      Tendsto (fun g : ℕ => External.wpVolume G g n (L g) /
        (External.cuspVolume G g n *
          ∏ i, (if L g i=0 then 1 else Real.sinh (L g i/2)/(L g i/2))))
        atTop (𝓝 1) ∧
      Tendsto (fun g : ℕ => External.wpVolume G g n (L g) /
        (Real.sqrt (2/Real.pi)*(4*Real.pi^2)^(2*g+n-3)*
          Real.Gamma (2*(g:ℝ)+n-5/2) *
          ∏ i, (if L g i=0 then 1 else Real.sinh (L g i/2)/(L g i/2))))
        atTop (𝓝 1)) := by
  have he (x : ℝ) := (boundary_factor_endpoints x).1
  constructor
  · have ht := fixed_cusp_all_length_bound P G n hn
    simpa only [he] using ht
  · intro L hLn hL
    refine ⟨?_,fixed_cusp_growing_boundary_kimura P G n hn L hLn hL⟩
    have ht := fixed_cusp_growing_boundary_limit P G n hn L hLn hL
    simpa only [he] using ht

end WP
