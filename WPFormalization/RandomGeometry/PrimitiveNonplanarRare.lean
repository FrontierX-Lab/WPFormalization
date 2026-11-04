import WPFormalization.RandomGeometry.PrimitiveSeparatingRare
import WPFormalization.RandomGeometry.PrimitiveNonseparatingRare

/-! Every sufficiently short nonplanar primitive curve is either an actual
nonseparating cut or an actual two-positive-genus separating cut. Their proven
mean bounds make all these competitors disappear at the original scale. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter Finset
open scoped Topology ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n : ℕ}

include C in
lemma primitive_short_nonplanar_cases (hg : 1≤g) (X : G.Moduli g n (fun _=>0))
    (γ : H.Primitive g n X) (hshort : H.length γ<2*Real.arsinh 1) (hnoplanar : H.planarSide γ=none) :
    WP.Critical.IsNonseparating T γ ∨IsPositiveGenusSeparating T γ := by
  obtain ⟨o,ho,_⟩ := T.orbit_partition X (fun _ : Fin 1=>γ)
    (fun i j _=>Subsingleton.elim _ _) (fun _=>C.shortPrimitive_simple γ hshort)
    (fun i j hne=>(hne (Subsingleton.elim _ _)).elim)
  rcases primitive_one_edge_nonplanar_cases T hg o X (fun _=>γ) ho hnoplanar with h1|h2
  · exact Or.inl ⟨o,ho,h1⟩
  · exact Or.inr ⟨⟨o,h2⟩,ho⟩

include C MI in
theorem primitiveNonplanar_probability_tendsto_zero (n : ℕ→ℕ)
    (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) (t : ℝ) (ht : 0≤t) :
    Tendsto (fun g=>(wpProbability G g (n g)).real {X |∃γ : H.Primitive g (n g) X,
      H.length γ≤t/Real.sqrt (pantsScale g (n g)) ∧H.planarSide γ=none}) atTop (𝓝 0) := by
  have hL : Tendsto (fun g=>t/Real.sqrt (pantsScale g (n g))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        (WP.Spectral.pantsScale_tendsto_atTop n hn))).const_mul t
  have hc : 0<2*Real.arsinh 1 := mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  have hlim := (primitiveNonseparating_probability_tendsto_zero T MI n hn t ht).add
    (primitiveSeparating_probability_tendsto_zero T MI n hn t ht)
  simp only [add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _=>ENNReal.toReal_nonneg)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ),hL.eventually (gt_mem_nhds hc)] with g hg hsmall
  letI := wpProbability_isFinite G g (n g)
  apply le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
  rintro X ⟨γ,hγ,hnop⟩
  rcases primitive_short_nonplanar_cases T C hg X γ (hγ.trans_lt hsmall) hnop with hns|hsep
  · exact Or.inl ⟨γ,hγ,hns⟩
  · exact Or.inr ⟨γ,hγ,hsep⟩

end WP.RandomGeometry
