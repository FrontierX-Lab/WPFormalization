import WPFormalization.Tight.SeparatingIntegralEnvelope

/- Normalization of the exact ordered orbit integrations. The positive original geometric volume is retained; no probability or separating estimate is an external premise. -/


noncomputable section
universe u v w z
namespace WP.TightSeparating
open Set Filter Finset MeasureTheory External TightMoments
open scoped Topology BigOperators ENNReal

lemma separating_orbit_integral_normalized_envelope {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (I : BuddLionsTightIntegration G T H Q A)
    (g k n : ℕ) (hg : 2 ≤ g) (s : Finset (A.Orbit g 0 k))
    (ell U : ℝ) (hell : 0 ≤ ell) (hU : 0 ≤ U)
    (hV : 0 < cuspVolume G g n)
    (hbound : ∀ x ∈ Critical.cutLengthBox k ell,
      (∑ o ∈ s, (A.cut o).tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x) /
        cuspVolume G g n ≤ U) :
    (ENNReal.ofReal (cuspVolume G g n))⁻¹ *
      (∑ o ∈ s, ∫⁻ X in T.region g 0 n (fun i => Fin.elim0 i) (fun _ => 0),
      A.orbitSum o (Critical.cutLengthTest k ell) X
        ∂G.wpMeasure g (0+n) (Fin.append (fun i => Fin.elim0 i) (fun _ => 0))) ≤
      ENNReal.ofReal (U*ell^(2*k)) := by
  have hraw : ∀ x ∈ Critical.cutLengthBox k ell,
      (∑ o ∈ s, (A.cut o).tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x) ≤
        U*cuspVolume G g n := fun x hx => (div_le_iff₀ hV).mp (hbound x hx)
  have h := separating_orbit_integral_envelope T A I g k n hg s ell
    (U*cuspVolume G g n) hell (mul_nonneg hU hV.le) hraw
  calc
    _ ≤ (ENNReal.ofReal (cuspVolume G g n))⁻¹ *
        ENNReal.ofReal (U*cuspVolume G g n*ell^(2*k)) := mul_le_mul' le_rfl h
    _ = _ := by
      rw [show U*cuspVolume G g n*ell^(2*k)=cuspVolume G g n*(U*ell^(2*k)) by ring,
        ENNReal.ofReal_mul hV.le,←mul_assoc,
        ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hV) ENNReal.ofReal_ne_top,one_mul]

end WP.TightSeparating
