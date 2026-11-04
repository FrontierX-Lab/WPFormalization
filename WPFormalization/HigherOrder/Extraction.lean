import WPFormalization.HigherOrder.Endpoint

/-! Canonical finite coefficient extraction, Section 10 Eqs.10.4--10.5.
The numerator uses the actual transport coefficients generated in Endpoint.lean;
no free family L/A/e is substituted for the paper's coefficients.
All operations at one order use finitely many derivatives and polynomial terms.
The critical-endpoint limit and common holomorphic continuation are proved
downstream in Volumes/CanonicalCoefficientExtension.lean.
-/
noncomputable section
namespace WP.HigherOrder
open PowerSeries Filter
open scoped Topology

/-- G_w(w^(2a))=(-1)^a(2a-1)!!, G_w(w^(2a+1))=0. -/
def gaussianMoment (n : ℕ) : ℝ :=
  if Even n then (-1 : ℝ)^(n/2)*∏ k ∈ Finset.range (n/2), (2*(k : ℝ)+1) else 0

def gaussianFunctional (f : Polynomial ℝ) : ℝ :=
  f.sum (fun n a => a*gaussianMoment n)

@[simp] theorem gaussianMoment_zero : gaussianMoment 0 = 1 := by simp [gaussianMoment]
@[simp] theorem gaussianMoment_one : gaussianMoment 1 = 0 := by norm_num [gaussianMoment]
@[simp] theorem gaussianMoment_two : gaussianMoment 2 = -1 := by norm_num [gaussianMoment]
@[simp] theorem gaussianMoment_four : gaussianMoment 4 = 3 := by norm_num [gaussianMoment,Finset.prod_range_succ]

/-- The order-τ^n polynomial in the exponent of Eq.10.4. -/
def extractionLogPolynomial (p : ℕ) (x : ℝ) (n : ℕ) : Polynomial ℝ :=
  if n = 0 then 0 else
    Polynomial.monomial (n+2)
      (((euler^[n+2]) extractionS x)/((n+2).factorial*(Real.sqrt (euler Psi x))^(n+2))) +
    Polynomial.monomial n
      (((euler^[n]) (fun x => Real.log (extractionB p x)) x)/
        (n.factorial*(Real.sqrt (euler Psi x))^n))

@[simp] theorem extractionLogPolynomial_zero (p : ℕ) (x : ℝ) :
    extractionLogPolynomial p x 0 = 0 := by simp [extractionLogPolynomial]

/-- Coefficients of the formal exponential in Eq.10.4, a finite power sum. -/
def extractionExpPolynomial (p : ℕ) (x : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n+1), Polynomial.C ((j.factorial : ℝ)⁻¹) *
    PowerSeries.coeff n ((PowerSeries.mk (extractionLogPolynomial p x))^j)

/-- Taylor expansion of Στ^(2s)L_{p,s}(x exp(τw/√v)) from Eq.10.4. -/
def markedTaylorPolynomial (P : PsiTheory) (p : ℕ) (x : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ s ∈ Finset.range (n/2+1),
    let q := n-2*s
    Polynomial.monomial q
      (((euler^[q]) (fun x => markedCoefficient P p s (inverseY x)) x)/
        (q.factorial*(Real.sqrt (euler Psi x))^q))

/- The actual Gaussian numerator N_p(τ,x), Eq.10.4. -/
@[blueprint "eq:CG3"]
def extractionNumerator (P : PsiTheory) (p : ℕ) (x : ℝ) : Series :=
  PowerSeries.mk (fun n => gaussianFunctional
    (∑ j ∈ Finset.range (n+1), extractionExpPolynomial p x j * markedTaylorPolynomial P p x (n-j)))

@[simp] theorem gaussianFunctional_C (a : ℝ) : gaussianFunctional (Polynomial.C a) = a := by
  unfold gaussianFunctional
  rw [Polynomial.sum_C_index (f := fun n a => a*gaussianMoment n) (by simp)]
  simp

@[simp] theorem gaussianFunctional_one : gaussianFunctional 1 = 1 := by
  simpa using gaussianFunctional_C 1

@[simp] theorem extractionExpPolynomial_zero (p : ℕ) (x : ℝ) :
    extractionExpPolynomial p x 0 = 1 := by
  simp [extractionExpPolynomial]

@[simp] theorem markedTaylorPolynomial_zero (P : PsiTheory) (p : ℕ) (x : ℝ) :
    markedTaylorPolynomial P p x 0 = 1 := by
  simp [markedTaylorPolynomial]

@[simp] theorem extractionNumerator_constant (P : PsiTheory) (p : ℕ) (x : ℝ) :
    constantCoeff (extractionNumerator P p x) = 1 := by
  simp [extractionNumerator, ← coeff_zero_eq_constantCoeff]

/-- Log of √(2πk)p_k, from the standard Bernoulli Stirling expansion.
Only odd inverse powers occur, with the negative sign appropriate to 1/k!. -/
def poissonStirlingLog : Series := PowerSeries.mk (fun n =>
  if Odd n then -(bernoulli (n+1) : ℝ)/((n : ℝ)*(n+1)) else 0)

def poissonStirlingSeries : Series := finiteExp poissonStirlingLog

@[simp] theorem poissonStirlingLog_constant : constantCoeff poissonStirlingLog = 0 := by
  norm_num [poissonStirlingLog, ← coeff_zero_eq_constantCoeff]
@[simp] theorem poissonStirlingSeries_constant : constantCoeff poissonStirlingSeries = 1 := by
  simp [poissonStirlingSeries]

/- Denominator Σs_i Ψ(x)^(-i)τ^(2i), Eq.10.5. -/
@[blueprint "eq:CG3"]
def extractionDenominator (x : ℝ) : Series := PowerSeries.mk (fun n =>
  if Even n then PowerSeries.coeff (n/2) poissonStirlingSeries * (Psi x)⁻¹^(n/2) else 0)

@[simp] theorem extractionDenominator_constant (x : ℝ) :
    constantCoeff (extractionDenominator x) = 1 := by
  simp [extractionDenominator, coeff_zero_eq_constantCoeff]

/- Eq.10.5 on its initial domain 0<Y<y₀. -/
@[blueprint "eq:CG3"]
def rawExtractedCoefficient (P : PsiTheory) (p j : ℕ) (Y : ℝ) : ℝ :=
  PowerSeries.coeff (2*j) (extractionNumerator P p (XR Y)*(extractionDenominator (XR Y))⁻¹)

@[simp] theorem rawExtractedCoefficient_zero (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    rawExtractedCoefficient P p 0 Y = 1 := by
  rw [rawExtractedCoefficient, Nat.mul_zero, coeff_zero_eq_constantCoeff]
  simp

/- The critical value is defined as the left limit. Existence and agreement with
an analytic extension are proved downstream in Volumes/CanonicalCoefficientExtension.lean. -/
@[blueprint "eq:CG3"]
def criticalExtractedCoefficient (P : PsiTheory) (p j : ℕ) : ℝ :=
  limUnder (𝓝[<] y₀) (rawExtractedCoefficient P p j)

@[simp] theorem criticalExtractedCoefficient_zero (P : PsiTheory) (p : ℕ) :
    criticalExtractedCoefficient P p 0 = 1 := by
  unfold criticalExtractedCoefficient
  have hf : rawExtractedCoefficient P p 0 = fun _ : ℝ => 1 :=
    funext (rawExtractedCoefficient_zero P p)
  rw [hf]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
    (𝓝[<] y₀) (𝓝 1)).limUnder_eq

/- The paper's prescribed values at zero and at the critical endpoint.
Downstream results prove agreement with the interior limits and the common complex extension. -/
@[blueprint "eq:CG3"]
def extractedCoefficient (P : PsiTheory) (p j : ℕ) (Y : ℝ) : ℝ :=
  if Y = 0 then markedCoefficient P p j 0 else
    if Y = y₀ then criticalExtractedCoefficient P p j else rawExtractedCoefficient P p j Y

@[simp] theorem extractedCoefficient_at_zero (P : PsiTheory) (p j : ℕ) :
    extractedCoefficient P p j 0 = markedCoefficient P p j 0 := by simp [extractedCoefficient]

@[simp] theorem extractedCoefficient_zero (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    extractedCoefficient P p 0 Y = 1 := by
  simp [extractedCoefficient]

/- A_j(g,n) in Theorem 1.1, including the exact unmarked finite-product rule. -/
@[blueprint "eq:AV7"]
def absoluteCoefficient (P : PsiTheory) (j g n : ℕ) : ℝ :=
  if n = 0 then unmarkedCoefficient P j else
    extractedCoefficient P 1 j (densityY (2*((n-1 : ℕ) : ℝ)/(2*(g : ℝ)-1)))

@[simp] theorem absoluteCoefficient_unmarked (P : PsiTheory) (j g : ℕ) :
    absoluteCoefficient P j g 0 = unmarkedCoefficient P j := by simp [absoluteCoefficient]

@[simp] theorem absoluteCoefficient_zero (P : PsiTheory) (g n : ℕ) :
    absoluteCoefficient P 0 g n = 1 := by
  simp [absoluteCoefficient]

end WP.HigherOrder
