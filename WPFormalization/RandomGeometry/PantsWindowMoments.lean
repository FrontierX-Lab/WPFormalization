import WPFormalization.RandomGeometry.PantsMomentIntegration

/-! Arbitrary nonnegative short-window tests in the exact ordered pants
integration identity; the original r curve slots remain ordered. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

def pantsWindowSum (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (F : (Fin r → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' γ : H.OrderedPlanarTuple X 2 L r, F (fun i => H.length (γ.val i))

lemma pantsOrbitShort_weighted_sum (o : PantsStarOrbit T g n r)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (F : (Fin r → ℝ) → ℝ≥0∞)
    (hsupport : ∀x, ¬ (∀i, x i ≤ L) → F x=0) :
    T.orbitSum o.val F X =
      ∑' γ : {γ : Fin r → H.Primitive g n X //
        T.orbitMem o.val X γ ∧ ∀i, H.length (γ i) ≤ L},
        F (fun i => H.length (γ.val i)) := by
  classical
  let p := fun γ : Fin r → H.Primitive g n X => T.orbitMem o.val X γ
  let q := fun γ : Fin r → H.Primitive g n X => ∀i, H.length (γ i) ≤ L
  let f := fun γ : Subtype p => F (fun i => H.length (γ.val i))
  have hs := tsum_subtype {γ : Subtype p | q γ.val} f
  let es : {γ : Subtype p | q γ.val} ≃ {γ : Subtype p // q γ.val} := Equiv.refl _
  have he := (es.trans (Equiv.subtypeSubtypeEquivSubtypeInter p q)).tsum_eq
    (fun γ => F (fun i => H.length (γ.val i)))
  calc
    _ = ∑' γ : Subtype p, ({γ : Subtype p | q γ.val}).indicator f γ := by
      apply tsum_congr
      intro γ
      by_cases hq : q γ.val
      · simp only [Set.indicator,Set.mem_ofPred_eq,hq,ite_true]
        rfl
      · simpa only [Set.indicator,Set.mem_ofPred_eq,hq,ite_false] using hsupport _ hq
    _ = ∑' γ : {γ : Subtype p | q γ.val}, f γ.val := hs.symm
    _ = _ := he

include C in
lemma pants_weighted_orbit_sum (hg : 1 ≤ g) (hr : 0 < r)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (F : (Fin r → ℝ) → ℝ≥0∞) (hsupport : ∀x, ¬ (∀i, x i ≤ L) → F x=0) :
    (∑' o : PantsStarOrbit T g n r, T.orbitSum o.val F X) = pantsWindowSum (H:=H) X L F := by
  simp_rw [pantsOrbitShort_weighted_sum T _ X L F hsupport]
  rw [← ENNReal.tsum_sigma]
  have he := (pantsTuplePartitionEquiv T C hg hr X L hL).tsum_eq
    (fun γ => F (fun i => H.length (γ.val i)))
  change (∑' p : PantsStarShortTuple T X L, F (fun i => H.length (p.2.val i))) = _
  convert he using 1
  · apply tsum_congr
    intro p
    rfl
  · rfl


include MI in
lemma pantsStarOrbit_test_lintegral (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (o : PantsStarOrbit T g n r) (hgn : (g,n) ≠ (2,0))
    (F : (Fin r → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ X, T.orbitSum o.val F X ∂G.wpMeasure g n (fun _ => 0)) =
      ∫⁻ x : Fin r → ℝ in {x | ∀i, 0 ≤ x i},
        F x * ENNReal.ofReal (boundaryVolumeModel P g (n-r)
          (activeBoundaryLengths (show r ≤ n-r by omega) x)) * ∏i, ENNReal.ofReal (x i) := by
  rw [MI.orbit_integral o.val (by unfold Stable; omega) (by intro h; cases Prod.mk.inj h; omega)
    hgn F hF,pantsStarOrbit_coefficient T hg,one_mul]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (pants_orthant_measurable r)] with x hx
  rw [pantsStarOrbit_volumeProduct T hg hn o x hx]

include C MI in
lemma pants_window_probability_integral (hg : 2 ≤ g) (hr : 0 < r) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (F : (Fin r → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hsupport : ∀x, ¬ (∀i, x i ≤ L) → F x=0) :
    (∫⁻ X : G.Moduli g n (fun _ => 0), pantsWindowSum (H:=H) X L F ∂wpProbability G g n) =
      (G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ *
        (Fintype.card (PantsStarOrbit T g n r) : ℝ≥0∞) *
          ∫⁻ x : Fin r → ℝ in {x | ∀i, 0 ≤ x i},
            F x * ENNReal.ofReal (boundaryVolumeModel P g (n-r)
              (activeBoundaryLengths (show r ≤ n-r by omega) x)) * ∏i, ENNReal.ofReal (x i) := by
  have hgn : (g,n) ≠ (2,0) := by intro h; have hh := congrArg Prod.snd h; simp only at hh; omega
  rw [wpProbability,lintegral_smul_measure]
  simp only [smul_eq_mul,mul_assoc]
  congr 1
  calc
    _ = ∫⁻ X, ∑' o : PantsStarOrbit T g n r, T.orbitSum o.val F X
        ∂G.wpMeasure g n (fun _ => 0) := by
      apply lintegral_congr
      intro X
      exact (pants_weighted_orbit_sum T C (by omega) hr X L hL F hsupport).symm
    _ = ∑' o : PantsStarOrbit T g n r,
        ∫⁻ X, T.orbitSum o.val F X ∂G.wpMeasure g n (fun _ => 0) :=
      lintegral_tsum (fun o => (MI.orbitSum_measurable o.val F hF).aemeasurable)
    _ = _ := by
      simp_rw [pantsStarOrbit_test_lintegral T MI hg hn _ hgn F hF]
      rw [tsum_fintype]
      simp [mul_assoc]

end WP.RandomGeometry
