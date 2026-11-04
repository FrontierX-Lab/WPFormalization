import WPFormalization.Tight.SeparatingKernelRates
import WPFormalization.Tight.SeparatingExpectationEnvelope
import WPFormalization.Tight.ConnectedPoissonScale
import WPFormalization.Tight.ConnectedUniformAssembly
import WPFormalization.Volumes.DiagonalChainAlgebra

/- Two-regime proof of the uniform all-cusp separating orbit estimate. The capped integral min(I,1) is used only in the sequential uniformity argument, and the final conclusion is an ENNReal bound on I itself, proving finiteness as well. -/


noncomputable section
universe u v w z
namespace WP.TightSeparating
open Set Filter Finset MeasureTheory External TightMoments
open scoped Topology BigOperators ENNReal

def separatingOrbitIntegral {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (T : TightRegions G) {H : HyperbolicCurveGeometry.{u,v,w} G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (g k n : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (cuspVolume G g n))⁻¹ *
    (∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter (fun o => 2 ≤ (A.cut o).components),
      ∫⁻ X in T.region g 0 n (fun i => Fin.elim0 i) (fun _ => 0),
      A.orbitSum o (Critical.cutLengthTest k ell) X
        ∂G.wpMeasure g (0+n) (Fin.append (fun i => Fin.elim0 i) (fun _ => 0)))

lemma separating_integral_rate_at_parameter {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Qgeom : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Qgeom A)
    (k : ℕ) (hk : 1 ≤ k) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      0 < cuspVolume G g n → ∀ s ∈ Ioo (0 : ℝ) xCritical,
      ∀ K : ℝ, 0 < K →
      (∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
        (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
        (∑ i, complexity (gs i) (ps i)) = complexity g 0 →
        ∀ L : (i : Fin Q) → Fin (ps i) → ℝ,
        realCoeff (cutProductG P gs ps L) n/realCoeff (Phi P g) n ≤
          K*((cutProductG P gs ps L (s : ℂ)).re/markedF P g 0 s)) →
      separatingOrbitIntegral T A g k n (L0/tightParameterScale (inverseY s)) ≤
        ENNReal.ofReal (K*C/(g : ℝ)) := by
  classical
  obtain ⟨C,hC,N,hvalue⟩ := separating_orbit_tight_value_sum A k hk L0
  refine ⟨C*(L0^(2*k)+1)/(4:ℝ)^k,by positivity,max N 2,?_⟩
  intro g hg n hV s hs K hK hT
  have hg2 : 2 ≤ g := le_of_max_le_right hg
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (show 0<g by omega)
  have hY := (inverseY_branch s ⟨hs.1.le,hs.2⟩).1
  have ha := tightParameterScale_pos _ hY
  have hr := r_pos _ hY
  let U : ℝ := K*C*(r (inverseY s))^k/((2*Real.pi^2)^k*(g : ℝ))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hbound : ∀ x ∈ Critical.cutLengthBox k (L0/tightParameterScale (inverseY s)),
      (∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter (fun o => 2 ≤ (A.cut o).components),
        (A.cut o).tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x)/
          cuspVolume G g n ≤ U := by
    intro x hx
    have hbox : ∀ e, 0 ≤ tightParameterScale (inverseY s)*x e ∧
        tightParameterScale (inverseY s)*x e ≤ L0 := by
      intro e
      refine ⟨mul_nonneg ha.le (hx.1 e),?_⟩
      have he := mul_le_mul_of_nonneg_left (hx.2 e) ha.le
      convert he using 1 <;> field_simp
    have hv := hvalue g (le_of_max_le_left hg) (inverseY s) hY x hbox
    rw [(inverseY_branch s ⟨hs.1.le,hs.2⟩).2] at hv
    exact separating_kernel_ratio_of_coefficient_transfer A BZ g k n hg2 hk s hs K C hK.le
      hT x (fun e => hx.1 e) hv
  have hi := separating_orbit_integral_normalized_envelope T A I g k n hg2
    ((univ : Finset (A.Orbit g 0 k)).filter (fun o => 2 ≤ (A.cut o).components))
    (L0/tightParameterScale (inverseY s)) U (div_nonneg hL0 ha.le) hU hV hbound
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have he := separating_physical_box_cancellation (inverseY s) hY k (K*C) L0
  change U*(L0/tightParameterScale (inverseY s))^(2*k) ≤ _
  calc
    _ = (K*C*L0^(2*k)/(4:ℝ)^k)/(g : ℝ) := by
      dsimp [U]
      rw [show K*C*r (inverseY s)^k/((2*Real.pi^2)^k*(g : ℝ)) =
        (K*C*r (inverseY s)^k/(2*Real.pi^2)^k)/(g : ℝ) by ring]
      rw [div_mul_eq_mul_div,he]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hgpos.le
      field_simp
      nlinarith [pow_nonneg hL0 (2*k)]


lemma separatingOrbitIntegral_mono {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (T : TightRegions G) {H : HyperbolicCurveGeometry.{u,v,w} G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (g k n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    separatingOrbitIntegral T A g k n a ≤ separatingOrbitIntegral T A g k n b := by
  classical
  unfold separatingOrbitIntegral
  apply mul_le_mul' le_rfl
  apply sum_le_sum
  intro o ho
  apply lintegral_mono
  intro X
  unfold TightMulticurveTopology.orbitSum
  apply ENNReal.tsum_le_tsum
  intro γ
  split_ifs with hγ
  · by_cases hx : (fun i => Q.length (γ i)) ∈ Critical.cutLengthBox k a
    · have hy : (fun i => Q.length (γ i)) ∈ Critical.cutLengthBox k b :=
        ⟨hx.1,fun i => (hx.2 i).trans hab⟩
      simp only [Critical.cutLengthTest,indicator_of_mem hx,indicator_of_mem hy]
      exact le_rfl
    · simp only [Critical.cutLengthTest,indicator_of_notMem hx]
      exact zero_le
  · exact le_rfl

lemma separating_volume_positive_eventually (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) :
    ∀ᶠ g : ℕ in atTop, ∀ n : ℕ, 0 < cuspVolume G g n := by
  obtain ⟨N,hF0⟩ := TightConnected.connected_unmarked_positive_eventually P
  filter_upwards [eventually_ge_atTop (max N 2)] with g hg
  have hg2 : 2 ≤ g := le_of_max_le_right hg
  intro n
  rw [Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)]
  rcases n with _ | n
  · have h0 : 0 < realCoeff (Phi P g) 0 := by
      simpa only [realCoeff,WP.coeff,markedF,iteratedDeriv_zero,Nat.factorial_zero,
        Nat.cast_one,div_one,Complex.ofReal_zero] using hF0 g (le_of_max_le_left hg) 0
          ⟨le_rfl,Analysis.xCritical_pos_parameter⟩
    rw [unmarked_realCoeff_volume] at h0
    exact (div_pos_iff_of_pos_right (by positivity)).mp h0
  · exact diagonal_volume_pos_nonempty P g (n+1) (by omega) (by unfold Stable;omega)



def separatingCappedExpectation {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (T : TightRegions G) {H : HyperbolicCurveGeometry.{u,v,w} G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (g k n : ℕ) (ell : ℝ) : ℝ := (min (separatingOrbitIntegral T A g k n ell) 1).toReal

lemma separating_integral_tendsto_of_transfer {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Qgeom : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Qgeom A)
    (k : ℕ) (hk : 1 ≤ k) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (gg nn : ℕ → ℕ) (hg : Tendsto gg atTop atTop)
    (ss : ℕ → ℝ) (hs : ∀ᶠ j in atTop, ss j ∈ Ioo (0 : ℝ) xCritical)
    (hscale : Tendsto (fun j => tightParameterScale (inverseY (ss j))/
      tightScale ((nn j : ℝ)/(gg j : ℝ))) atTop (𝓝 1))
    (K : ℝ) (hK : 0 < K)
    (hT : ∀ᶠ j in atTop, ∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
      (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
      (∑ i, complexity (gs i) (ps i)) = complexity (gg j) 0 →
      ∀ L : (i : Fin Q) → Fin (ps i) → ℝ,
      realCoeff (cutProductG P gs ps L) (nn j)/realCoeff (Phi P (gg j)) (nn j) ≤
        K*((cutProductG P gs ps L ((ss j : ℝ) : ℂ)).re/markedF P (gg j) 0 (ss j))) :
    Tendsto (fun j => separatingCappedExpectation T A (gg j) k (nn j)
      (L0/tightScale ((nn j : ℝ)/(gg j : ℝ)))) atTop (𝓝 0) := by
  obtain ⟨C,hC,N,hrate⟩ := separating_integral_rate_at_parameter T A BZ I k hk (2*L0) (by positivity)
  have hupper : ∀ᶠ j in atTop,
      separatingCappedExpectation T A (gg j) k (nn j)
        (L0/tightScale ((nn j : ℝ)/(gg j : ℝ))) ≤ K*C/(gg j : ℝ) := by
    filter_upwards [hg.eventually_ge_atTop (max N 2),hs,hT,
      hg.eventually (separating_volume_positive_eventually P G),
      hscale.eventually (gt_mem_nhds (by norm_num : (1 : ℝ)<2))] with j hj hs hT hV hscale
    have hd := TightConnected.tightScale_pos ((nn j : ℝ)/(gg j : ℝ)) (by positivity)
    have ha := tightParameterScale_pos _ (inverseY_branch _ ⟨hs.1.le,hs.2⟩).1
    have hα : tightParameterScale (inverseY (ss j)) ≤
        2*tightScale ((nn j : ℝ)/(gg j : ℝ)) :=
      (div_le_iff₀ hd).mp hscale.le
    have hell : L0/tightScale ((nn j : ℝ)/(gg j : ℝ)) ≤
        (2*L0)/tightParameterScale (inverseY (ss j)) := by
      apply (div_le_div_iff₀ hd ha).mpr
      nlinarith [mul_le_mul_of_nonneg_left hα hL0]
    have hb := (separatingOrbitIntegral_mono T A (gg j) k (nn j) _ _ hell).trans
      (hrate (gg j) (le_of_max_le_left hj) (nn j) (hV _) (ss j) hs K hK hT)
    have hb' := ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) ((min_le_left _ (1 : ℝ≥0∞)).trans hb)
    rw [ENNReal.toReal_ofReal (by positivity)] at hb'
    exact hb'
  exact squeeze_zero' (Eventually.of_forall (fun j => ENNReal.toReal_nonneg)) hupper
    ((tendsto_natCast_atTop_atTop.comp hg).const_div_atTop (K*C))



lemma separating_integral_tendsto_diverging {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Qgeom : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Qgeom A)
    (k : ℕ) (hk : 1 ≤ k) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (gg nn : ℕ → ℕ) (hg : Tendsto gg atTop atTop) (hn : Tendsto nn atTop atTop) :
    Tendsto (fun j => separatingCappedExpectation T A (gg j) k (nn j)
      (L0/tightScale ((nn j : ℝ)/(gg j : ℝ)))) atTop (𝓝 0) := by
  let gg' : ℕ → ℕ := fun j => max 3 (gg j)
  let nn' : ℕ → ℕ := fun j => max 2 (nn j)
  have hg' : Tendsto gg' atTop atTop := tendsto_atTop_mono (fun j => le_max_right _ _) hg
  have hn' : Tendsto nn' atTop atTop := tendsto_atTop_mono (fun j => le_max_right _ _) hn
  have hg3 : ∀ j, 3 ≤ gg' j := fun j => le_max_left _ _
  have hg2 : ∀ j, 2 ≤ gg' j := fun j => by have := hg3 j; omega
  have hn2 : ∀ j, 2 ≤ nn' j := fun j => le_max_left _ _
  obtain ⟨K,hK,hT⟩ := separating_coefficient_transfer_unbounded P
  have hlim := separating_integral_tendsto_of_transfer T A BZ I k hk L0 hL0 gg' nn' hg'
    (fun j => TightConnected.connectedSaddle (gg' j) (nn' j))
    (Eventually.of_forall (fun j => (TightConnected.connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1))
    (TightConnected.connectedSaddle_scale_ratio_tendsto gg' nn' hg' hg3 hn2)
    K hK (hT gg' nn' hg' hn' hg2 hn2)
  apply hlim.congr'
  filter_upwards [hg.eventually_ge_atTop 3,hn.eventually_ge_atTop 2] with j hj hnj
  simp only [gg',nn',max_eq_right hj,max_eq_right hnj]

lemma separating_integral_tendsto_fixed {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Qgeom : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Qgeom A)
    (k : ℕ) (hk : 1 ≤ k) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (n : ℕ) (gg : ℕ → ℕ) (hg : Tendsto gg atTop atTop) :
    Tendsto (fun j => separatingCappedExpectation T A (gg j) k n
      (L0/tightScale ((n : ℝ)/(gg j : ℝ)))) atTop (𝓝 0) := by
  obtain ⟨K,hK,hT⟩ := separating_coefficient_transfer_bounded P n 1 (by norm_num)
  have hh := (Analysis.complexity_real_tendsto_atTop 0).comp hg
  have hs : ∀ᶠ j in atTop, 1/(complexity (gg j) 0 : ℝ) ∈ Ioo (0 : ℝ) xCritical := by
    filter_upwards [hh.eventually_gt_atTop 0,
      TightConnected.connected_small_weight_eventually (fun j => (complexity (gg j) 0 : ℝ))
        hh 1 (by norm_num)] with j hj hx
    exact ⟨div_pos (by norm_num) hj,hx.2⟩
  apply separating_integral_tendsto_of_transfer T A BZ I k hk L0 hL0 gg (fun _ => n) hg
    (fun j => 1/(complexity (gg j) 0 : ℝ)) hs
    (TightConnected.connected_bounded_poisson_scale_ratio_tendsto gg hg n 1 (by norm_num)) K hK
  filter_upwards [hT gg hg] with j hj
  intro Q gs ps hp hs hsum L
  exact hj Q gs ps hp hs L



lemma separatingOrbitIntegral_zero_edges {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (T : TightRegions G) {H : HyperbolicCurveGeometry.{u,v,w} G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (g n : ℕ) (ell : ℝ) : separatingOrbitIntegral T A g 0 n ell=0 := by
  unfold separatingOrbitIntegral
  rw [Orbit.separating_zero_edges A g]
  simp

lemma tight_separating_orbit_uniform {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Qgeom : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Qgeom A)
    (k : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      separatingOrbitIntegral T A g k n (L0/tightScale ((n : ℝ)/(g : ℝ))) ≤
        ENNReal.ofReal ε := by
  classical
  by_cases hk : k=0
  · subst k
    intro ε hε
    refine ⟨0,?_⟩
    intro g hg n
    rw [separatingOrbitIntegral_zero_edges]
    exact zero_le
  have hk1 : 1 ≤ k := by omega
  have hfixed : ∀ n : ℕ, ∀ (gs : ℕ → ℕ) (as : ℕ → Unit), Tendsto gs atTop atTop →
      (∀ j : ℕ, True) → Tendsto (fun j => separatingCappedExpectation T A (gs j) k n
        (L0/tightScale ((n : ℝ)/(gs j : ℝ)))) atTop (𝓝 0) := by
    intro n gs as hg ha
    exact separating_integral_tendsto_fixed T A BZ I k hk1 L0 hL0 n gs hg
  have hdiv : ∀ (gs ns : ℕ → ℕ) (as : ℕ → Unit), Tendsto gs atTop atTop →
      Tendsto ns atTop atTop → (∀ j : ℕ, True) →
      Tendsto (fun j => separatingCappedExpectation T A (gs j) k (ns j)
        (L0/tightScale ((ns j : ℝ)/(gs j : ℝ)))) atTop (𝓝 0) := by
    intro gs ns as hg hn ha
    exact separating_integral_tendsto_diverging T A BZ I k hk1 L0 hL0 gs ns hg hn
  have hunif := TightConnected.connected_uniform_of_fixed_and_diverging
    (fun g n (_ : Unit) => separatingCappedExpectation T A g k n
      (L0/tightScale ((n : ℝ)/(g : ℝ)))) (fun _ => True) hfixed hdiv
  intro ε hε
  let δ : ℝ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨N,hN⟩ := hunif δ hδ
  refine ⟨N,?_⟩
  intro g hg n
  let J := separatingOrbitIntegral T A g k n (L0/tightScale ((n : ℝ)/(g : ℝ)))
  have hcap : (min J 1).toReal ≤ δ := by
    have he := hN g hg n () trivial
    rw [abs_of_nonneg (show 0 ≤ separatingCappedExpectation T A g k n _ from ENNReal.toReal_nonneg)] at he
    exact he
  have hmfin : min J 1 ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hm : min J 1 ≤ ENNReal.ofReal δ := by
    rw [←ENNReal.ofReal_toReal hmfin]
    exact ENNReal.ofReal_le_ofReal hcap
  have hδ1 : ENNReal.ofReal δ < 1 := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr
      ((min_le_right (ε/2) (1/2)).trans_lt (by norm_num))
  have hJ : J < 1 := by
    have hmin : min J 1 < 1 := hm.trans_lt hδ1
    exact (min_lt_iff.mp hmin).resolve_right (lt_irrefl _)
  rw [min_eq_left hJ.le] at hm
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  exact (min_le_left _ _).trans (by linarith)

end WP.TightSeparating
