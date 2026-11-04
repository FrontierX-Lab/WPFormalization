import WPFormalization.Statements.Basic

/-! Finite Taylor coefficients of a jointly analytic function along its diagonal.
The first coordinate derivative is evaluated in the actual direction `(1, 0)`.
Full open-neighborhood slice identities preserve analyticity at every parameter. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def firstPartial (f:ℂ × ℂ → ℂ) (p:ℂ × ℂ):ℂ:=fderiv ℂ f p (1,0)
def firstPartialJet (f:ℂ × ℂ → ℂ):ℕ → (ℂ × ℂ → ℂ)
  | 0 => f
  | m + 1 => firstPartial (firstPartialJet f m)
lemma firstPartial_analyticAt (f:ℂ × ℂ → ℂ) (p:ℂ × ℂ) (hf:AnalyticAt ℂ f p):
    AnalyticAt ℂ (firstPartial f) p:=by
  exact ((ContinuousLinearMap.apply ℂ ℂ ((1,0):ℂ × ℂ)).analyticAt _).comp hf.fderiv
lemma firstPartialJet_analyticOnNhd (f:ℂ × ℂ → ℂ) (U:Set (ℂ × ℂ))
    (hf:AnalyticOnNhd ℂ f U) (m:ℕ):AnalyticOnNhd ℂ (firstPartialJet f m) U:=by
  induction m with
  | zero => exact hf
  | succ m ih => intro p hp;exact firstPartial_analyticAt _ p (ih p hp)
lemma iteratedDeriv_slice_eq_firstPartialJet (f:ℂ × ℂ → ℂ) (U:Set (ℂ × ℂ))
    (hU:IsOpen U) (hf:AnalyticOnNhd ℂ f U) (m:ℕ) (w ν:ℂ) (hp:(w,ν)∈U):
    iteratedDeriv m (fun z:ℂ=>f (z,ν)) w=firstPartialJet f m (w,ν):=by
  induction m generalizing w ν with
  | zero => rfl
  | succ m ih =>
    rw[iteratedDeriv_succ]
    have he:(iteratedDeriv m (fun z:ℂ=>f (z,ν)))=ᶠ[𝓝 w]
        (fun z:ℂ=>firstPartialJet f m (z,ν)):=by
      have hmem: {z:ℂ|(z,ν)∈U}∈𝓝 w:=
        (hU.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp
      filter_upwards[hmem] with z hz
      exact ih z ν hz
    rw[he.deriv_eq]
    have hcurve:HasDerivAt (fun z:ℂ=>(z,ν)) ((1,0):ℂ × ℂ) w:=
      (hasDerivAt_id w).prodMk (hasDerivAt_const w ν)
    have hh:=((firstPartialJet_analyticOnNhd f U hf m) (w,ν) hp).differentiableAt.hasFDerivAt.comp_hasDerivAt w hcurve
    exact hh.deriv
lemma diagonalCoeff_eq_firstPartialJet (f:ℂ × ℂ → ℂ) (U:Set (ℂ × ℂ))
    (hU:IsOpen U) (hf:AnalyticOnNhd ℂ f U) (m:ℕ) (ν:ℂ) (hp:(ν,ν)∈U):
    WP.coeff (fun z:ℂ=>f (ν+z,ν)) m=firstPartialJet f m (ν,ν)/(m.factorial:ℂ):=by
  rw[WP.coeff]
  have he := congrFun (iteratedDeriv_comp_const_add m (fun t:ℂ=>f (t,ν)) ν) 0
  simp only[add_zero] at he
  rw[he]
  rw[iteratedDeriv_slice_eq_firstPartialJet f U hU hf m ν ν hp]
lemma diagonalCoeff_analyticAt (f:ℂ × ℂ → ℂ) (U:Set (ℂ × ℂ))
    (hU:IsOpen U) (hf:AnalyticOnNhd ℂ f U) (m:ℕ) (ν:ℂ) (hp:(ν,ν)∈U):
    AnalyticAt ℂ (fun v:ℂ=>WP.coeff (fun z:ℂ=>f (v+z,v)) m) ν:=by
  have hj:AnalyticAt ℂ (fun v:ℂ=>firstPartialJet f m (v,v)) ν :=
    ((firstPartialJet_analyticOnNhd f U hf m) (ν,ν) hp).comp
      (f:=fun v:ℂ=>(v,v)) (analyticAt_id.prod analyticAt_id)
  have ha:AnalyticAt ℂ (fun v:ℂ=>firstPartialJet f m (v,v)/(m.factorial:ℂ)) ν:=hj.div_const
  apply ha.congr
  have hmem:{v:ℂ|(v,v)∈U}∈𝓝 ν:=
    (hU.preimage (continuous_id.prodMk continuous_id)).mem_nhds hp
  filter_upwards[hmem] with v hv
  exact (diagonalCoeff_eq_firstPartialJet f U hU hf m v hv).symm
end WP.Analysis
namespace WP.Analysis
open Set
lemma diagonalCoeff_analyticOnNhd_polydisk (f:ℂ × ℂ → ℂ)
    (R1 R2 r:ℝ) (hr1:r≤R1) (hr2:r≤R2)
    (hf:AnalyticOnNhd ℂ f ((Metric.ball (0:ℂ) R1)×ˢ(Metric.ball (0:ℂ) R2)))
    (m:ℕ):AnalyticOnNhd ℂ
      (fun ν:ℂ=>WP.coeff (fun z:ℂ=>f (ν+z,ν)) m) (Metric.ball (0:ℂ) r):=by
  intro ν hν
  have hn:‖ν‖<r:=by simpa only[Metric.mem_ball,dist_zero_right] using hν
  apply diagonalCoeff_analyticAt f _ (Metric.isOpen_ball.prod Metric.isOpen_ball) hf m ν
  exact ⟨by simpa only[Metric.mem_ball,dist_zero_right] using hn.trans_le hr1,
    by simpa only[Metric.mem_ball,dist_zero_right] using hn.trans_le hr2⟩
end WP.Analysis
