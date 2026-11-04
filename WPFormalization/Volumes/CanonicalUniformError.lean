import WPFormalization.Volumes.CompactCanonicalExpansion
import WPFormalization.Volumes.CriticalDensitySector
import WPFormalization.Volumes.OriginCanonicalExpansion
import WPFormalization.HigherOrder.MarkedExpansionProof
/-! The THREE actual extraction sectors give the original coefficient error uniformly at EVERY nonnegative frequency. Positive density-inverse specifications map the two endpoint sectors to one interior compact interval; one C/B/c/H is selected before g/k/K. The original extractedCoefficient and the full K<=c*sqrt(h) window are unchanged. Common complex coefficient extension and optimal truncation are separate clauses of the final theorem. -/
noncomputable section
namespace WP.Analysis
open Set
lemma canonical_uniform_coefficient_error (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c H : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < H ∧
      ∀ g k K : ℕ, H ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c * Real.sqrt (complexity g p : ℝ) →
      let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
      |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
        ∑ j ∈ Finset.range (K+1), HigherOrder.extractedCoefficient P p j Y / (complexity g p : ℝ)^j| ≤
          C * B^(K+1) * ((K+1).factorial : ℝ)^2 / (complexity g p : ℝ)^(K+1) := by
  obtain ⟨ν0,Co,Bo,co,Ho,hν0,hCo,hBo,hco,hHo,ho⟩ := actual_origin_extracted_expansion P p hp
  obtain ⟨R,Cc,Bc,cc,Hc,hR,hRy,hCc,hBc,hcc,hHc,hcError⟩ := actual_critical_density_sector_expansion P p hp
  let Ya := densityY ν0
  have hYa := densityY_spec ν0 hν0.le
  have hYap : 0 < Ya := by
    by_contra hn
    have he : Ya = 0 := le_antisymm (le_of_not_gt hn) hYa.1.1
    have hd : WP.density Ya = ν0 := hYa.2
    rw [he,density_zero_value] at hd
    linarith
  let xa := XR Ya
  let xb := XR (y₀-R)
  have hxap : 0 < xa := by
    simpa only [XR_zero] using XR_strictMonoOn (show (0 : ℝ) ∈ Iic y₀ from y₀_pos.le)
      (show Ya ∈ Iic y₀ from hYa.1.2.le) hYap
  have hyb : y₀-R ∈ Ioo (0 : ℝ) y₀ := ⟨by linarith,by linarith⟩
  have hxbp : 0 < xb := by
    simpa only [XR_zero] using XR_strictMonoOn (show (0 : ℝ) ∈ Iic y₀ from y₀_pos.le)
      (show y₀-R ∈ Iic y₀ from hyb.2.le) hyb.1
  have hxbc : xb < xCritical := XR_strictMonoOn
    (show y₀-R ∈ Iic y₀ from hyb.2.le) (show y₀ ∈ Iic y₀ from by simp) hyb.2
  let α : ℝ := min xa xb / 2
  let β : ℝ := (xb+xCritical)/2
  have hα : 0 < α := half_pos (lt_min hxap hxbp)
  have hαa : α ≤ xa := (half_le_self (lt_min hxap hxbp).le).trans (min_le_left _ _)
  have hαb : α ≤ xb := (half_le_self (lt_min hxap hxbp).le).trans (min_le_right _ _)
  have hxbβ : xb < β := by dsimp [β]; linarith
  have hβc : β < xCritical := by dsimp [β]; linarith
  have hαβ : α ≤ β := hαb.trans hxbβ.le
  obtain ⟨Cm,Bm,cm,Hm,hCm,hBm,hcm,hHm,hm⟩ := actual_compact_extracted_expansion P p hp α β hα hαβ hβc
  let C : ℝ := Co+Cm+Cc
  let B : ℝ := Bo+Bm+Bc
  let c : ℝ := min co (min cm cc)
  let H : ℝ := Ho+Hm+Hc
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := lt_min hco (lt_min hcm hcc)
  have hH : 0 < H := by dsimp [H]; positivity
  have hCoC : Co ≤ C := by dsimp [C]; linarith
  have hCmC : Cm ≤ C := by dsimp [C]; linarith
  have hCcC : Cc ≤ C := by dsimp [C]; linarith
  have hBoB : Bo ≤ B := by dsimp [B]; linarith
  have hBmB : Bm ≤ B := by dsimp [B]; linarith
  have hBcB : Bc ≤ B := by dsimp [B]; linarith
  refine ⟨C,B,c,H,hC,hB,hc,hH,?_⟩
  intro g k K hg hK
  let h : ℝ := complexity g p
  let Y : ℝ := densityY (2*(k : ℝ)/h)
  have hhO : Ho ≤ h := by dsimp [H] at hg; linarith
  have hhM : Hm ≤ h := by dsimp [H] at hg; linarith
  have hhC : Hc ≤ h := by dsimp [H] at hg; linarith
  have hh : 0 < h := hH.trans_le hg
  have hKO : (K : ℝ) ≤ co * Real.sqrt h := hK.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg h))
  have hKM : (K : ℝ) ≤ cm * Real.sqrt h := hK.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (Real.sqrt_nonneg h))
  have hKC : (K : ℝ) ≤ cc * Real.sqrt h := hK.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (Real.sqrt_nonneg h))
  by_cases hsmall : (k : ℝ)/h ≤ ν0
  · exact (ho g k K hhO hsmall hKO).trans
      (HigherOrder.gevreyTwo_majorant_mono Co Bo C B h (K+1) hBo.le hC.le hCoC hBoB hh)
  by_cases hlarge : y₀-R < Y
  · exact (hcError g k K hhC hKC hlarge).trans
      (HigherOrder.gevreyTwo_majorant_mono Cc Bc C B h (K+1) hBc.le hC.le hCcC hBcB hh)
  have hd := densityY_spec (2*(k : ℝ)/h) (by positivity)
  have hν : ν0 < (k : ℝ)/h := lt_of_not_ge hsmall
  have hYaY : Ya ≤ Y := by
    by_contra hn
    have he := density_strictMonoOn hd.1 hYa.1 (lt_of_not_ge hn)
    rw [hd.2,hYa.2] at he
    have he' : 2*(k : ℝ)/h = 2*((k : ℝ)/h) := by ring
    rw [he'] at he
    linarith
  have hYupper : Y ≤ y₀-R := le_of_not_gt hlarge
  let x : ℝ := XR Y
  have hxa : xa ≤ x := XR_strictMonoOn.monotoneOn
    (show Ya ∈ Iic y₀ from hYa.1.2.le) (show Y ∈ Iic y₀ from hd.1.2.le) hYaY
  have hxb : x ≤ xb := XR_strictMonoOn.monotoneOn
    (show Y ∈ Iic y₀ from hd.1.2.le) (show y₀-R ∈ Iic y₀ from hyb.2.le) hYupper
  have hx : x ∈ Icc α β := ⟨hαa.trans hxa,hxb.trans hxbβ.le⟩
  have hInv : inverseY x = Y := inverseY_eq_of_root x Y hd.1.2.le rfl
  have hPsi : WP.Psi x = (2*(k : ℝ)/h)/2 := by
    dsimp only [WP.Psi]
    rw [hInv,hd.2]
  have hroot : (k : ℝ) = h * WP.Psi x := by rw [hPsi]; field_simp [hh.ne'] <;> ring
  have he := hm g k K hhM hKM x hx hroot
  rw [hInv] at he
  exact he.trans (HigherOrder.gevreyTwo_majorant_mono Cm Bm C B h (K+1) hBm.le hC.le hCmC hBmB hh)
end WP.Analysis
