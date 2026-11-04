import WPFormalization.Tight.ConnectedPoissonTight
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

/-- A compact scaled-length representative, eventually the desired rescaling. -/
def connectedTransportScaledLengths {p:ℕ} (qs:ℕ→ℝ) (ts:ℕ→Fin p→ℝ) (j:ℕ) (i:Fin p) : ℝ :=
  if qs j∈Icc (0:ℝ) 2 then qs j*ts j i else 0

lemma connectedTransportScaledLengths_box (p:ℕ) (B:ℝ) (hB:0≤B)
    (qs:ℕ→ℝ) (ts:ℕ→Fin p→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    ∀j i,connectedTransportScaledLengths qs ts j i∈Icc (0:ℝ) (2*B) := by
  intro j i
  unfold connectedTransportScaledLengths
  split_ifs with hq
  · exact ⟨mul_nonneg hq.1 (ht j i).1,mul_le_mul hq.2 (ht j i).2 (ht j i).1 (by norm_num)⟩
  · exact ⟨le_rfl,by positivity⟩

/-- Exact normalization transport for coefficient families. It uses a proved
reference coefficient limit; no new asymptotic assertion is introduced. -/
lemma connected_coefficient_scale_transport {p:ℕ} (k:ℕ) (B:ℝ) (hB:0≤B)
    (A:ℕ→(Fin p→ℝ)→ℝ) (D rs rd αs αd:ℕ→ℝ)
    (hαd:∀j,0<αd j) (hαs:∀ᶠj in atTop,0<αs j)
    (hrs:∀ᶠj in atTop,rs j≠0) (hrd:∀ᶠj in atTop,rd j≠0)
    (hq:Tendsto (fun j=>αs j/αd j) atTop (𝓝 1))
    (hr:Tendsto (fun j=>rs j/rd j) atTop (𝓝 1))
    (ts:ℕ→Fin p→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B)
    (hsource:Tendsto (fun j=>
      A j (fun i=>connectedTransportScaledLengths (fun j=>αs j/αd j) ts j i/αs j)/
        (D j*((rs j)^k*∏i,boundaryFactor 0 (connectedTransportScaledLengths (fun j=>αs j/αd j) ts j i))))
      atTop (𝓝 1)) :
    Tendsto (fun j=>A j (fun i=>ts j i/αd j)/(D j*((rd j)^k*∏i,boundaryFactor 0 (ts j i))))
      atTop (𝓝 1) := by
  have hqbox : ∀ᶠj in atTop,αs j/αd j∈Icc (0:ℝ) 2 := by
    filter_upwards [hαs,hq.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2))] with j hj hk
    exact ⟨(div_pos hj (hαd j)).le,hk.le⟩
  have hf := connected_scaled_factors_tendsto p B (fun j=>αs j/αd j) hq hqbox ts ht
  have hnorm : Tendsto (fun j=>(∏i,boundaryFactor 0 (connectedTransportScaledLengths (fun j=>αs j/αd j) ts j i))/
      (∏i,boundaryFactor 0 (ts j i))) atTop (𝓝 1) := by
    apply hf.congr'
    filter_upwards [hqbox] with j hj
    simp only [connectedTransportScaledLengths,if_pos hj]
  have hfinal := (hsource.mul (hr.pow k)).mul hnorm
  simp only [one_pow,one_mul] at hfinal
  apply hfinal.congr'
  filter_upwards [hαs,hqbox,hrs,hrd,hsource.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with j hsj hqj hrsj hrdj hpos
  have hD : D j≠0 := by
    intro hz
    rw [hz,zero_mul,div_zero] at hpos
    linarith
  have hlen : (fun i=>connectedTransportScaledLengths (fun j=>αs j/αd j) ts j i/αs j)=
      (fun i=>ts j i/αd j) := by
    funext i
    simp only [connectedTransportScaledLengths,if_pos hqj]
    field_simp [hsj.ne',(hαd j).ne']
  have hsprod : (∏i,boundaryFactor 0 (connectedTransportScaledLengths (fun j=>αs j/αd j) ts j i))≠0 :=
    (Finset.prod_pos (fun i _=>boundaryFactor_pos _ _)).ne'
  have hdprod : (∏i,boundaryFactor 0 (ts j i))≠0 := (Finset.prod_pos (fun i _=>boundaryFactor_pos _ _)).ne'
  rw [hlen]
  simp only [div_pow]
  field_simp [hD,hrsj,hrdj,hsprod,hdprod]
end WP.TightConnected
