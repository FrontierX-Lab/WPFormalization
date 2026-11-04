import WPFormalization.HigherOrder.WeightedCoefficientSum

/-! Weighted coefficient sums over complete normed coefficient rings. Geometric coefficient decay and polynomial lower-order data give actual summability and a common growing-order norm bound. These are generic estimates, with no hierarchy convergence premise. -/
noncomputable section
namespace WP.HigherOrder
lemma weighted_coefficient_tsum_norm_bound {𝕜:Type*} [NormedCommRing 𝕜] [CompleteSpace 𝕜]
    (a:ℕ→𝕜) (f:ℕ→PowerSeries 𝕜) (n k:ℕ) (C B S:ℝ)
    (hB:0≤B) (hS:0≤S)
    (hs:Summable (fun l:ℕ=>(S+l+1)^k*‖a l‖))
    (hbound:(∑'l:ℕ,(S+l+1)^k*‖a l‖)≤C*S^k)
    (hf:∀l:ℕ,‖PowerSeries.coeff n (f l)‖≤B*(S+l+1)^k) :
    Summable (fun l:ℕ=>a l*PowerSeries.coeff n (f l)) ∧
    ‖∑'l:ℕ,a l*PowerSeries.coeff n (f l)‖≤C*B*S^k := by
  have hpoint (l:ℕ) : ‖a l*PowerSeries.coeff n (f l)‖≤B*((S+l+1)^k*‖a l‖) := by
    apply (norm_mul_le _ _).trans
    convert! mul_le_mul_of_nonneg_left (hf l) (norm_nonneg (a l)) using 1 <;>ring
  have hnorm:Summable (fun l:ℕ=>‖a l*PowerSeries.coeff n (f l)‖):=
    Summable.of_nonneg_of_le (fun l=>norm_nonneg _) hpoint (hs.mul_left B)
  refine ⟨Summable.of_norm hnorm,?_⟩
  calc _≤∑'l:ℕ,‖a l*PowerSeries.coeff n (f l)‖:=norm_tsum_le_tsum_norm hnorm
    _≤∑'l:ℕ,B*((S+l+1)^k*‖a l‖):=hnorm.tsum_le_tsum hpoint (hs.mul_left B)
    _=B*(∑'l:ℕ,(S+l+1)^k*‖a l‖):=tsum_mul_left
    _≤B*(C*S^k):=mul_le_mul_of_nonneg_left hbound hB
    _=C*B*S^k:=by ring

lemma geometric_coefficient_tsum_order_bounds {𝕜:Type*} [NormedCommRing 𝕜] [CompleteSpace 𝕜]
    (R K:ℝ) (hR:1<R) (hK:0<K) :
    ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧ ∀M:ℝ,M₀≤M→∀a:ℕ→𝕜,(∀l,‖a l‖≤K/R^l)→
      ∀j D p k n:ℕ,1≤p→k≤2*j→∀B:ℝ,0≤B→∀f:ℕ→PowerSeries 𝕜,
      (∀l:ℕ,‖PowerSeries.coeff n (f l)‖≤B*((D:ℝ)+p+M*j+l+1)^k)→
      Summable (fun l:ℕ=>a l*PowerSeries.coeff n (f l)) ∧
      ‖∑'l:ℕ,a l*PowerSeries.coeff n (f l)‖≤C*B*((D:ℝ)+p+M*j)^k := by
  obtain ⟨C,M₀,hC,hM₀,hscale⟩:=Analysis.geometric_growing_order_scale_bound R K hR hK
  refine ⟨C,M₀,hC,hM₀,?_⟩
  intro M hM a ha j D p k n hp hk B hB f hf
  have hMpos:0<M:=lt_of_lt_of_le hM₀ hM
  have hS:0≤(D:ℝ)+p+M*j:=by positivity
  have hm:=hscale M hM (fun l=>‖a l‖) (by simpa only[abs_of_nonneg (norm_nonneg _)] using ha)
    j D p k hp hk
  simp only[abs_of_nonneg (norm_nonneg _)] at hm
  exact weighted_coefficient_tsum_norm_bound a f n k C B _ hB hS hm.1 hm.2 hf
end WP.HigherOrder
