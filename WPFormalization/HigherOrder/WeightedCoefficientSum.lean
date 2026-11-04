import WPFormalization.Analysis.NormalizedMomentScale
import WPFormalization.HigherOrder.Triangular

/-! The actual kernel and dilaton coefficient-sum operators preserve the growing-order polynomial normalization. Summability is proved from the lower coefficient bound and the actual common moment estimate, rather than assumed. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma coefficientSum_abs_bound (a:ℕ→ℝ) (f:ℕ→Series) (n k:ℕ) (C B S:ℝ)
    (hB:0≤B) (hS:0≤S)
    (hs:Summable (fun l:ℕ=>(S+l+1)^k*|a l|))
    (hbound:(∑'l:ℕ,(S+l+1)^k*|a l|)≤C*S^k)
    (hf:∀l:ℕ,|PowerSeries.coeff n (f l)|≤B*(S+l+1)^k) :
    Summable (fun l:ℕ=>a l*PowerSeries.coeff n (f l)) ∧
    |PowerSeries.coeff n (coefficientSum (fun l=>PowerSeries.C (a l)*f l))|≤C*B*S^k := by
  have hpoint (l:ℕ) : |a l*PowerSeries.coeff n (f l)|≤B*((S+l+1)^k*|a l|) := by
    rw [abs_mul]
    convert mul_le_mul_of_nonneg_left (hf l) (abs_nonneg (a l)) using 1 <;>ring
  have habs : Summable (fun l:ℕ=>|a l*PowerSeries.coeff n (f l)|):=
    Summable.of_nonneg_of_le (fun l=>abs_nonneg _) hpoint (hs.mul_left B)
  have hactual : Summable (fun l:ℕ=>a l*PowerSeries.coeff n (f l)):=by
    exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  have hnorm : Summable (fun l:ℕ=>‖a l*PowerSeries.coeff n (f l)‖) := by
    simpa only [Real.norm_eq_abs] using habs
  refine ⟨hactual,?_⟩
  simp only [coefficientSum_coeff,PowerSeries.coeff_C_mul]
  calc _≤∑'l:ℕ,|a l*PowerSeries.coeff n (f l)|:=by
         simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
       _≤∑'l:ℕ,B*((S+l+1)^k*|a l|):=habs.tsum_le_tsum hpoint (hs.mul_left B)
       _=B*(∑'l:ℕ,(S+l+1)^k*|a l|):=tsum_mul_left
       _≤B*(C*S^k):=mul_le_mul_of_nonneg_left hbound hB
       _=C*B*S^k:=by ring

lemma canonical_coefficientSum_order_bounds : ∃ C M₀:ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j D p k n:ℕ,1≤p→k≤2*j→∀B:ℝ,0≤B→∀f:ℕ→Series,
    ∀Y∈Set.Icc (0:ℝ) y₀,
      (∀l:ℕ,|PowerSeries.coeff n (f l)|≤B*((D:ℝ)+p+M*j+l+1)^k)→
      Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n (f l)) ∧
      Summable (fun l:ℕ=>canonicalDilatonCoefficient Y l*PowerSeries.coeff n (f l)) ∧
      |PowerSeries.coeff n (coefficientSum (fun l=>PowerSeries.C (weight Y l)*f l))|≤C*B*((D:ℝ)+p+M*j)^k ∧
      |PowerSeries.coeff n (coefficientSum (fun l=>PowerSeries.C (canonicalDilatonCoefficient Y l)*f l))|≤C*B*((D:ℝ)+p+M*j)^k := by
  obtain ⟨C,M₀,hC,hM₀,hdata⟩:=Analysis.canonical_growing_order_scale_bounds
  refine ⟨C,M₀,hC,hM₀,?_⟩
  intro M hM j D p k n hp hk B hB f Y hY hf
  have hMp : 0<M:=lt_of_lt_of_le hM₀ hM
  have hS : 0≤(D:ℝ)+p+M*j:=by positivity
  obtain ⟨hws,hbs,hw,hb⟩:=hdata M hM j D p k hp hk Y hY
  have hW:=coefficientSum_abs_bound (weight Y) f n k C B _ hB hS hws hw hf
  have hB':=coefficientSum_abs_bound (canonicalDilatonCoefficient Y) f n k C B _ hB hS hbs hb hf
  exact ⟨hW.1,hB'.1,hW.2,hB'.2⟩
end WP.HigherOrder
