import Mathlib
/-! Exact multinomial counting of the original individually labeled cusps, proved from multivariate polynomial coefficients. The exponential coefficient identity restores each local factorial weight. -/

noncomputable section
namespace WP.Critical
open Finset

/-- The histogram of the actual n individually labeled cusps. -/
def cutCuspHistogram {n Q : ℕ} (σ : Fin n→Fin Q) : Fin Q→₀ℕ :=
  ∑i:Fin n,Finsupp.single (σ i) 1

lemma cutCuspHistogram_eq_card {n Q:ℕ} (σ:Fin n→Fin Q) (c:Fin Q) :
    cutCuspHistogram σ c=Fintype.card {i:Fin n // σ i=c} := by
  classical
  simp [cutCuspHistogram,Finsupp.sum_apply,Finsupp.single_apply,
    Fintype.card_subtype]

lemma cutCuspHistogram_monomial {n Q:ℕ} (σ:Fin n→Fin Q) :
    (∏i:Fin n,(MvPolynomial.X (σ i):MvPolynomial (Fin Q) ℕ))=
      MvPolynomial.monomial (cutCuspHistogram σ) 1 := by
  rw [cutCuspHistogram,MvPolynomial.monomial_sum_one]
  rfl

/-- The exact multinomial count, obtained from coefficients of (sum X_i)^n.
This counts every original cusp label, including when some fibers are empty. -/
lemma cutCuspLabels_card (n Q:ℕ) (q:Fin Q→₀ℕ) :
    (univ.filter (fun σ:Fin n→Fin Q=>cutCuspHistogram σ=q)).card =
      if q.sum (fun _ m=>m)=n then q.multinomial else 0 := by
  classical
  have he := congrArg (fun p:MvPolynomial (Fin Q) ℕ=>p.coeff q)
    (Fintype.sum_pow (fun c:Fin Q=>(MvPolynomial.X c:MvPolynomial (Fin Q) ℕ)) n)
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype,MvPolynomial.coeff_sum] at he
  simp_rw [cutCuspHistogram_monomial,MvPolynomial.coeff_monomial] at he
  simpa using he.symm

lemma cutCuspLabels_card_of_sum (n Q:ℕ) (q:Fin Q→₀ℕ)
    (hq:q.sum (fun _ m=>m)=n) :
    (univ.filter (fun σ:Fin n→Fin Q=>cutCuspHistogram σ=q)).card =
      q.multinomial := by rw [cutCuspLabels_card,if_pos hq]

lemma cutCuspLabels_card_real (n Q:ℕ) (q:Fin Q→₀ℕ)
    (hq:q.sum (fun _ m=>m)=n) :
    ((univ.filter (fun σ:Fin n→Fin Q=>cutCuspHistogram σ=q)).card:ℝ)=
      (n.factorial:ℝ)/(∏c:Fin Q,(q c).factorial:ℝ) := by
  rw [cutCuspLabels_card_of_sum n Q q hq]
  have he := Nat.multinomial_spec (univ:Finset (Fin Q)) q
  have hq' : (∑c:Fin Q,q c)=n := by
    rw [←hq]
    exact (Finsupp.sum_of_support_subset q (subset_univ q.support)
      (fun _ m=>m) (by simp)).symm
  rw [hq'] at he
  rw [Finsupp.multinomial_eq_of_support_subset (subset_univ q.support)]
  apply (eq_div_iff (by positivity : (∏c:Fin Q,(q c).factorial:ℝ)≠0)).mpr
  exact_mod_cast (by nlinarith only [he])

end WP.Critical
namespace WP.Critical
open Finset

lemma cutCuspHistogram_sum {n Q:ℕ} (σ:Fin n→Fin Q) :
    (∑c:Fin Q,cutCuspHistogram σ c)=n := by
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv σ)
  simpa only [Fintype.card_sigma,Fintype.card_fin,cutCuspHistogram_eq_card] using he

lemma cutCuspHistogram_mem {n Q:ℕ} (σ:Fin n→Fin Q) :
    cutCuspHistogram σ∈finsuppAntidiag univ n :=
  mem_finsuppAntidiag.mpr ⟨cutCuspHistogram_sum σ,subset_univ _⟩

/-- Exact exponential coefficient formula for the allocation of individually
labeled original cusps. The factorial factors restore the local weights. -/
lemma cutCuspLabels_series_coeff (n Q:ℕ) (f:Fin Q→PowerSeries ℝ) :
    (∑σ:Fin n→Fin Q,
      ∏c:Fin Q,( (cutCuspHistogram σ c).factorial:ℝ)*
        PowerSeries.coeff (cutCuspHistogram σ c) (f c)) =
      (n.factorial:ℝ)*PowerSeries.coeff n (∏c:Fin Q,f c) := by
  classical
  let weight : (Fin Q→₀ℕ)→ℝ := fun q=>
    ∏c:Fin Q,((q c).factorial:ℝ)*PowerSeries.coeff (q c) (f c)
  have hmaps : ∀σ∈(univ:Finset (Fin n→Fin Q)),cutCuspHistogram σ∈finsuppAntidiag univ n :=
    fun σ _=>cutCuspHistogram_mem σ
  have he := sum_fiberwise_of_maps_to' hmaps weight
  change (∑σ:Fin n→Fin Q,weight (cutCuspHistogram σ))=_
  rw [←he,PowerSeries.coeff_prod,mul_sum]
  apply sum_congr rfl
  intro q hq
  have hqn := (mem_finsuppAntidiag'.mp hq).1
  simp only [sum_const,nsmul_eq_mul]
  rw [cutCuspLabels_card_real n Q q hqn]
  dsimp only [weight]
  rw [prod_mul_distrib]
  have hp : (∏c:Fin Q,((q c).factorial:ℝ))≠0 := by positivity
  field_simp

end WP.Critical
