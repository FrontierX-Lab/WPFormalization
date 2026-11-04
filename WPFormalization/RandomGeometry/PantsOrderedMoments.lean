import WPFormalization.RandomGeometry.PantsWindowIntegration

/-! The exact ordered pants moment formula for every natural order r,
including the empty tuple. The geometric volume and WP law remain explicit. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

lemma pantsWindowCount_zero (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (I : Fin 0 → Set ℝ) :
    pantsWindowCount H X L I=1 := by
  unfold pantsWindowCount
  let e := Equiv.subtypeUnivEquiv (fun γ : H.OrderedPlanarTuple X 2 L 0 =>
    show ∀i : Fin 0, H.length (γ.val i) ∈ I i from fun i => i.elim0)
  rw [Nat.card_congr e,H.orderedPantsTuple_card,Nat.descFactorial_zero]

lemma pantsWindowVolumeIntegral_zero (P : PsiTheory) (g n : ℕ)
    (h0 : 0 ≤ n) (I : Fin 0 → Set ℝ) :
    pantsWindowVolumeIntegral P g n 0 h0 I=volumeModel P g n := by
  unfold pantsWindowVolumeIntegral
  rw [Measure.volume_pi_eq_dirac (fun i : Fin 0 => i.elim0)]
  simp only [Fin.forall_fin_zero,Set.setOf_true,Measure.restrict_univ,integral_dirac,
    Fin.prod_univ_zero,mul_one]
  have ha : activeBoundaryLengths h0 (fun i : Fin 0 => i.elim0)=(fun _ : Fin n => 0) := by
    funext j
    simp [activeBoundaryLengths]
  rw [ha,WP.Geometry.boundaryVolumeModel_zero]

include C MI in
lemma pants_ordered_window_moments_model (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) (hsub : ∀i, I i ⊆ Set.Icc 0 L) :
    (∫X : G.Moduli g n (fun _ => 0), (pantsWindowCount H X L I : ℝ) ∂wpProbability G g n) =
      ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*volumeModel P g n))*
        pantsWindowVolumeIntegral P g (n-r) r (show r ≤ n-r by omega) I := by
  by_cases hr : r=0
  · subst r
    simp_rw [pantsWindowCount_zero G H]
    rw [pantsWindowVolumeIntegral_zero]
    have hmass : (G.wpMeasure g n (fun _ => 0) Set.univ).toReal=volumeModel P g n :=
      WP.Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)
    simp only [Nat.mul_zero,Nat.descFactorial_zero,Nat.cast_one,pow_zero,one_mul,Nat.sub_zero]
    rw [integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_def,wpProbability,Measure.smul_apply,
      ENNReal.toReal_mul,ENNReal.toReal_inv,hmass]
    ring
  · exact pants_windows_moment_model G H T C MI hg (by omega) hn L hL I hI hsub

include C MI in
/- Equation (14.6): all ordered slots, all natural orders, and arbitrary Borel
windows in a common short interval. The right side uses the actual geometric
cut volume, with exactly the factor (n)_(2r)/2^r and no r! divisor. -/
@[blueprint "eq:PS3"]
theorem pants_ordered_window_moments (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) (hsub : ∀i, I i ⊆ Set.Icc 0 L) :
    (∫X : G.Moduli g n (fun _ => 0), (pantsWindowCount H X L I : ℝ) ∂wpProbability G g n) =
      ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*cuspVolume G g n))*
        pantsGeometricWindowIntegral G g (n-r) r (show r ≤ n-r by omega) I := by
  rw [WP.Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega),
    pantsGeometricWindowIntegral_eq_model P G g (n-r) r (show r ≤ n-r by omega)
      (by unfold Stable;omega) I hI (fun i x hx => (hsub i hx).1)]
  exact pants_ordered_window_moments_model G H T C MI hg hn L hL I hI hsub

end WP.RandomGeometry
