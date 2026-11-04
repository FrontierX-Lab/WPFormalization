import WPFormalization.Volumes.CuspLocalLimitAssembly
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Proposition 9.2: unrestricted simultaneous approach to either cusp-weight endpoint. -/
/- Blueprint label(s): prop:local-limit
Paper v3: 9.2 [PDF 41]
Status: CONDITIONALLY_PROVED; PsiTheory and registered classical inputs remain
-/
@[blueprint "prop:local-limit"]
theorem cusp_local_limit (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (gs : ℕ → ℕ) (xs : ℕ → ℝ) (ks : ℕ → ℕ) (u : ℝ)
    (hg : Tendsto gs atTop atTop) (hx : ∀ j, xs j ∈ Set.Ioo 0 xCritical)
    (hmu : Tendsto (fun j => complexity (gs j) p*Psi (xs j)) atTop atTop)
    (hu : Tendsto (fun j => ((ks j : ℝ)-complexity (gs j) p*Psi (xs j)) /
      Real.sqrt (complexity (gs j) p*euler Psi (xs j))) atTop (𝓝 u)) :
    Tendsto (fun j => Real.sqrt (complexity (gs j) p*euler Psi (xs j))*
      cuspMass P (gs j) p (ks j) (xs j)) atTop
      (𝓝 (Real.exp (-u^2/2)/Real.sqrt (2*Real.pi))) := by
  exact cusp_local_limit_of_quantitative_proof P p hp gs xs ks u hg hx hmu hu

end WP
