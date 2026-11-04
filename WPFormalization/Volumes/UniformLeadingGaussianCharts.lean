import WPFormalization.Volumes.LeadingGaussianLocalCharts
/-! A genuine common leading Gaussian chart on the entire physical interval.
The three actual endpoint/interior constructions are patched with one radius
and one pair of bounds chosen before genus and cusp weight. The same radius
lies inside the actual Fourier period on the scale min(h,h*Psi(x)). -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace WP
open Set Filter Complex
open scoped Topology
set_option autoImplicit false
lemma uniform_actual_leading_gaussian_charts (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃ρ C D:ℝ,0<ρ ∧ 0<C ∧ 0<D ∧
      ∀g:ℕ,Stable g p→0<(complexity g p:ℝ)→∀x∈Ioo (0:ℝ) xCritical,
        let h:ℝ:=complexity g p
        let m:ℝ:=min h (h*Psi x)
        0 < m→LeadingGaussianChart g p x (ρ*Real.sqrt m) C D ∧
          ρ*Real.sqrt m≤Real.pi*Real.sqrt (h*euler Psi x):=by
  obtain ⟨ηo,ρo,Co,Do,K,hηo,hηox,hρo,hCo,hDo,hK,hmean,horigin⟩:=actual_origin_leading_charts P p
  obtain ⟨ηc,ρc,Cc,Dc,hηc,hηcy,hρc,hCc,hDc,hcritical⟩:=actual_critical_leading_charts P p
  let b:ℝ:=XR (y₀-ηc)
  have hb:0<b:=by
    have ht:=XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le)
      (show y₀-ηc∈Iic y₀ from by change y₀-ηc≤y₀;linarith only[hηc]) (by linarith only[hηcy]:0<y₀-ηc)
    simpa only[XR_zero] using ht
  have hbx:b<xCritical:=by
    exact XR_strictMonoOn (show y₀-ηc∈Iic y₀ from by change y₀-ηc≤y₀;linarith only[hηc])
      (show y₀∈Iic y₀ from mem_Iic.mpr le_rfl) (by linarith only[hηc]:y₀-ηc<y₀)
  let a:ℝ:=min (ηo/2) (b/2)
  have ha:0<a:=lt_min (half_pos hηo) (half_pos hb)
  have hao:a<ηo:=(min_le_left _ _).trans_lt (half_lt_self hηo)
  have hab:a≤b:=(min_le_right _ _).trans (by linarith only[hb])
  obtain ⟨ρi,Ci,Di,v,hρi,hCi,hDi,hv,hinterior⟩:=actual_compact_leading_charts P p hp a b ha hab hbx
  let c:ℝ:=min (1/K) (min 1 v)
  have hc:0<c:=lt_min (by positivity) (lt_min zero_lt_one hv)
  have hcK:c≤1/K:=min_le_left _ _
  have hc1:c≤1:=(min_le_right _ _).trans (min_le_left _ _)
  have hcv:c≤v:=(min_le_right _ _).trans (min_le_right _ _)
  let ro:ℝ:=ρo/Real.sqrt K
  have hro:0<ro:=div_pos hρo (Real.sqrt_pos.mpr hK)
  let ρ:ℝ:=min ro (min ρi (min ρc (Real.pi*Real.sqrt c)))
  have hρ:0<ρ:=lt_min hro (lt_min hρi (lt_min hρc (by positivity)))
  have hρo':ρ≤ro:=min_le_left _ _
  have hρi':ρ≤ρi:=(min_le_right _ _).trans (min_le_left _ _)
  have hρc':ρ≤ρc:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρfreq:ρ≤Real.pi*Real.sqrt c:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let C:ℝ:=max Co (max Ci Cc)
  let D:ℝ:=max Do (max Di Dc)
  have hCo':Co≤C:=le_max_left _ _
  have hCi':Ci≤C:=(le_max_left _ _).trans (le_max_right _ _)
  have hCc':Cc≤C:=(le_max_right _ _).trans (le_max_right _ _)
  have hDo':Do≤D:=le_max_left _ _
  have hDi':Di≤D:=(le_max_left _ _).trans (le_max_right _ _)
  have hDc':Dc≤D:=(le_max_right _ _).trans (le_max_right _ _)
  refine ⟨ρ,C,D,hρ,hCo.trans_le hCo',hDo.trans_le hDo',?_⟩
  intro g hs hh x hx
  dsimp only
  let h:ℝ:=complexity g p
  let m:ℝ:=min h (h*Psi x)
  intro hm
  have hmh:m≤h:=min_le_left _ _
  have hmμ:m≤h*Psi x:=min_le_right _ _
  have hrootm:0≤Real.sqrt m:=Real.sqrt_nonneg _
  have hvar:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hpair:LeadingGaussianChart g p x (ρ*Real.sqrt m) C D ∧ c*m≤h*euler Psi x:=by
    by_cases hxa:x<a
    · have hxo:x∈Ioo (0:ℝ) ηo:=⟨hx.1,hxa.trans hao⟩
      have hd:1≤deriv Psi x:=(hmean x hxo).1
      have hpmean:Psi x≤K*x:=(hmean x hxo).2
      have hmk:m≤K*(h*x):=by
        have ht:=mul_le_mul_of_nonneg_left hpmean hh.le
        nlinarith only[hmμ,ht]
      have hroot:Real.sqrt m≤Real.sqrt K*Real.sqrt (h*x):=by
        rw[←Real.sqrt_mul hK.le]
        exact Real.sqrt_le_sqrt hmk
      have hRad:ρ*Real.sqrt m≤ρo*Real.sqrt (h*x):=by
        calc
          _≤ro*Real.sqrt m:=mul_le_mul_of_nonneg_right hρo' hrootm
          _≤ro*(Real.sqrt K*Real.sqrt (h*x)):=mul_le_mul_of_nonneg_left hroot hro.le
          _=ρo*Real.sqrt (h*x):=by
            dsimp[ro]
            field_simp [(Real.sqrt_pos.mpr hK).ne']
      refine ⟨LeadingGaussianChart.mono _ _ _ _ _ _ _ _ _ (horigin x hxo g hs hh) hRad hCo' hDo',?_⟩
      have hmK:m/K≤h*x:=by apply (div_le_iff₀ hK).mpr;nlinarith only[hmk]
      have hcm:c*m≤ m/K:=by
        convert mul_le_mul_of_nonneg_right hcK hm.le using 1 <;>ring
      have hxv:x≤euler Psi x:=by
        simpa only[euler,mul_one] using mul_le_mul_of_nonneg_left hd hx.1.le
      exact (hcm.trans hmK).trans (mul_le_mul_of_nonneg_left hxv hh.le)
    · let δ:ℝ:=y₀-inverseY x
      have hY:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
      have hδ:0<δ:=by dsimp[δ];linarith only[hY.2]
      have hxeq:XR (y₀-δ)=x:=by
        have he:y₀-δ=inverseY x:=by dsimp[δ];ring
        rw[he]
        exact (inverseY_branch x ⟨hx.1.le,hx.2⟩).2
      by_cases hδc:δ<ηc
      · obtain ⟨hvcrit,hchart⟩:=hcritical δ ⟨hδ,hδc⟩
        rw[hxeq] at hvcrit hchart
        have hRad:ρ*Real.sqrt m≤ρc*Real.sqrt h:=
          (mul_le_mul_of_nonneg_right hρc' hrootm).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmh) hρc.le)
        refine ⟨LeadingGaussianChart.mono _ _ _ _ _ _ _ _ _ (hchart g hs hh) hRad hCc' hDc',?_⟩
        have hcm:c*m≤ m:=by simpa only[one_mul] using mul_le_mul_of_nonneg_right hc1 hm.le
        exact (hcm.trans hmh).trans (by simpa only[mul_one] using mul_le_mul_of_nonneg_left hvcrit hh.le)
      · have hxb:x≤b:=by
          have hδle:ηc≤δ:=le_of_not_gt hδc
          have hyle:inverseY x≤y₀-ηc:=by dsimp[δ] at hδle;linarith only[hδle]
          have ht:=XR_strictMonoOn.monotoneOn hY.2.le
            (show y₀-ηc∈Iic y₀ from by change y₀-ηc≤y₀;linarith only[hηc]) hyle
          simpa only[(inverseY_branch x ⟨hx.1.le,hx.2⟩).2,b] using ht
        obtain ⟨hvx,hchart⟩:=hinterior x ⟨le_of_not_gt hxa,hxb⟩
        have hRad:ρ*Real.sqrt m≤ρi*Real.sqrt h:=
          (mul_le_mul_of_nonneg_right hρi' hrootm).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmh) hρi.le)
        refine ⟨LeadingGaussianChart.mono _ _ _ _ _ _ _ _ _ (hchart g hs hh) hRad hCi' hDi',?_⟩
        have h₁:c*m≤v*m:=mul_le_mul_of_nonneg_right hcv hm.le
        have h₂:v*m≤v*h:=mul_le_mul_of_nonneg_left hmh hv.le
        have h₃:v*h≤h*euler Psi x:=by simpa only[mul_comm v h] using mul_le_mul_of_nonneg_left hvx hh.le
        exact h₁.trans (h₂.trans h₃)
  refine ⟨hpair.1,?_⟩
  have hsqrt:Real.sqrt c*Real.sqrt m≤Real.sqrt (h*euler Psi x):=by
    rw[←Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hpair.2
  calc
    _≤(Real.pi*Real.sqrt c)*Real.sqrt m:=mul_le_mul_of_nonneg_right hρfreq hrootm
    _≤Real.pi*Real.sqrt (h*euler Psi x):=by
      simpa only[mul_assoc] using mul_le_mul_of_nonneg_left hsqrt Real.pi_pos.le
end WP
