import WPFormalization.RandomGeometry.GeneralPlanarStarOrbits
import WPFormalization.RandomGeometry.GeneralPlanarStarIntegralDefinitions
import WPFormalization.RandomGeometry.CutVolumeTransport
import WPFormalization.RandomGeometry.PantsWindowCount
import WPFormalization.RandomGeometry.PantsMomentIntegration

/-! Actual orbit integration for general planar stars. No nested configurations
are identified with stars, and no paper moment asymptotic is assumed. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

def generalPlanarStarOrthantIntegral (P : PsiTheory) (g n r : ℕ)
    (k : Fin r → ℕ) (F : (Fin r → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻x : Fin r → ℝ in {x | ∀i,0≤x i},
    F x * ENNReal.ofReal (generalPlanarStarVolumeIntegrand P g n r k x) *
      ∏i,ENNReal.ofReal (x i)

/-- The literal generic integration sum over actual mapping-class orbits whose
cut is the canonical star, not the sum over all planar configurations. -/
def generalPlanarStarWindowSum (g n r : ℕ) (k : Fin r → ℕ)
    (F : (Fin r → ℝ) → ℝ≥0∞) (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑'o : GeneralPlanarStarOrbit T g n r k,T.orbitSum o.val F X

lemma generalPlanarStarOrbit_volumeProduct {k : Fin r → ℕ}
    (hg : 2≤g) (hk : ∀i,2≤k i) (o : GeneralPlanarStarOrbit T g n r k)
    (x : Fin r → ℝ) (hx : ∀i,0≤x i) :
    (T.cut o.val).volumeProduct G x=generalPlanarStarVolumeIntegrand P g n r k x := by
  exact ((generalPlanarOrbitLabelIso T o).volumeProduct_eq G x hx
    (generalPlanarStarCut_stable g n r k _ hg hk)).symm.trans
      (generalPlanarStar_volumeProduct P G g n r k (generalPlanarOrbitLabel T o) hg hk x hx)

include MI in
lemma generalPlanarStarOrbit_lintegral {k : Fin r → ℕ}
    (hg : 2≤g) (hk : ∀i,2≤k i) (o : GeneralPlanarStarOrbit T g n r k)
    (hgn : (g,n) ≠ (2,0)) (F : (Fin r → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻X,T.orbitSum o.val F X ∂G.wpMeasure g n (fun _ => 0)) =
      generalPlanarStarOrthantIntegral P g n r k F := by
  rw [MI.orbit_integral o.val (by unfold Stable;omega)
    (by intro h;cases Prod.mk.inj h;omega) hgn F hF,
    generalPlanarStarOrbit_coefficient T hg hk,one_mul]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (pants_orthant_measurable r)] with x hx
  rw [generalPlanarStarOrbit_volumeProduct T hg hk o x hx]

include MI in
set_option backward.isDefEq.respectTransparency false in
lemma generalPlanarStar_wp_lintegral {k : Fin r → ℕ}
    (hg : 2≤g) (hk : ∀i,2≤k i) (hgn : (g,n) ≠ (2,0))
    (F : (Fin r → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻X,generalPlanarStarWindowSum T g n r k F X ∂G.wpMeasure g n (fun _ => 0)) =
      (Fintype.card (GeneralPlanarStarOrbit T g n r k) : ℝ≥0∞) *
        generalPlanarStarOrthantIntegral P g n r k F := by
  calc
    _ = ∑'o : GeneralPlanarStarOrbit T g n r k,
      ∫⁻X,T.orbitSum o.val F X ∂G.wpMeasure g n (fun _ => 0) :=
      lintegral_tsum (fun o => (MI.orbitSum_measurable o.val F hF).aemeasurable)
    _ = ∑'_ : GeneralPlanarStarOrbit T g n r k,generalPlanarStarOrthantIntegral P g n r k F := by
      apply tsum_congr
      intro o
      exact generalPlanarStarOrbit_lintegral T MI hg hk o hgn F hF
    _ = _ := by rw [tsum_fintype];simp

include MI in
lemma generalPlanarStar_probability_lintegral {k : Fin r → ℕ}
    (hg : 2≤g) (hk : ∀i,2≤k i) (hgn : (g,n) ≠ (2,0))
    (F : (Fin r → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻X,generalPlanarStarWindowSum T g n r k F X ∂wpProbability G g n) =
      (G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ *
        (Fintype.card (GeneralPlanarStarOrbit T g n r k) : ℝ≥0∞) *
          generalPlanarStarOrthantIntegral P g n r k F := by
  rw [wpProbability,lintegral_smul_measure,generalPlanarStar_wp_lintegral T MI hg hk hgn F hF]
  simp only [smul_eq_mul,mul_assoc]

lemma generalPlanarStarOrbit_card_real (g n r : ℕ) (k : Fin r → ℕ)
    (hg : 2≤g) (hk : ∀i,2≤k i) :
    (Fintype.card (GeneralPlanarStarOrbit T g n r k) : ℝ) =
      (n.descFactorial (∑i,k i) : ℝ)/(∏i,((k i).factorial : ℝ)) := by
  have hpos : (0:ℝ)<∏i,((k i).factorial : ℝ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast Nat.factorial_pos (k i)
  apply (eq_div_iff (ne_of_gt hpos)).2
  exact_mod_cast generalPlanarStarOrbit_card T g n r k hg hk
end WP.RandomGeometry
