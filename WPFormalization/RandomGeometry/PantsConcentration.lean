import WPFormalization.RandomGeometry.PantsMomentAsymptoticsConcentration
import WPFormalization.RandomGeometry.PantsMoments

/-! The main concentration assertion of Proposition 14.2 for the actual WP
probability measure and actual short-pants count. The exact geometric moments
are supplied by the local orbit calculation, not assumed as extra hypotheses. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open Filter MeasureTheory WP.External
open scoped Topology

/-- The actual count divided by the actual q_g L_g² converges to one in
probability throughout the original fast-cusp regime. -/
theorem pants_concentration (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (MI : MirzakhaniIntegration G H T) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (L : ℕ → ℝ) (hLp : ∀ᶠ g in atTop, 0 < L g) (hL : Tendsto L atTop (𝓝 0))
    (hscale : Tendsto (fun g => pantsScale g (n g)*(L g)^2) atTop atTop) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun g => (wpProbability G g (n g)).real
        {X | ε ≤ |(H.pantsCount X (L g) : ℝ)/(pantsScale g (n g)*(L g)^2)-1|})
        atTop (𝓝 0) := by
  have hn := pants_fast_cusps_tendsto_atTop n hnfast
  have hshort : ∀ᶠ g in atTop, L g < 2*Real.arsinh 1 :=
    hL.eventually (gt_mem_nhds (mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))))
  apply pants_concentration_of_cut_integrals P G H T C n L hn hLp hL hscale
  · filter_upwards [eventually_ge_atTop (2:ℕ),hn.eventually_ge_atTop 2,hshort] with g hg hng hsg
    exact pants_first_moment_eq_cut G H T C MI hg hng (L g) hsg
  · filter_upwards [eventually_ge_atTop (2:ℕ),hn.eventually_ge_atTop 4,hshort] with g hg hng hsg
    exact pants_second_factorial_moment_eq_cut G H T C MI hg hng (L g) hsg

end WP.RandomGeometry
