import WPFormalization.HigherOrder.MajorantDefinitions

/-! Finite coefficient algebra for the analytic-majorant lemma.
Coefficients of products with at least two zero-constant factors depend strictly
on lower degrees; the ENNReal versions require no finiteness assumption.
-/
noncomputable section
namespace WP.Majorant
open scoped ENNReal

variable {R : Type*} [CommSemiring R]

def AgreeBelow (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ j < n, PowerSeries.coeff j f = PowerSeries.coeff j g

def LeBelow (n : ℕ) (f g : PowerSeries ℝ≥0∞) : Prop :=
  ∀ j < n, PowerSeries.coeff j f ≤ PowerSeries.coeff j g

lemma agreeBelow_mul {n : ℕ} {f g F G : PowerSeries R}
    (hf : AgreeBelow n f F) (hg : AgreeBelow n g G) : AgreeBelow n (f*g) (F*G) := by
  intro j hj
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [hf p.1 (by omega),hg p.2 (by omega)]

lemma leBelow_mul {n : ℕ} {f g F G : PowerSeries ℝ≥0∞}
    (hf : LeBelow n f F) (hg : LeBelow n g G) : LeBelow n (f*g) (F*G) := by
  intro j hj
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_le_sum
  intro p hp
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact mul_le_mul' (hf p.1 (by omega)) (hg p.2 (by omega))

lemma agreeBelow_listprod {σ : Type*} {n : ℕ} (l : List σ) (f g : σ → PowerSeries R)
    (h : ∀ s, AgreeBelow n (f s) (g s)) :
    AgreeBelow n (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => intro j hj; rfl
  | cons a l ih =>
      simp only [List.map_cons,List.prod_cons]
      exact agreeBelow_mul (h a) ih

lemma leBelow_listprod {σ : Type*} {n : ℕ} (l : List σ) (f g : σ → PowerSeries ℝ≥0∞)
    (h : ∀ s, LeBelow n (f s) (g s)) :
    LeBelow n (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => intro j hj; exact le_rfl
  | cons a l ih =>
      simp only [List.map_cons,List.prod_cons]
      exact leBelow_mul (h a) ih

lemma listprod_constant_zero {σ : Type*} (l : List σ) (f : σ → PowerSeries R)
    (h : ∀ s, PowerSeries.coeff 0 (f s) = 0) (hl : l ≠ []) :
    PowerSeries.coeff 0 (l.map f).prod = 0 := by
  cases l with
  | nil => contradiction
  | cons a l =>
      simp only [List.map_cons,List.prod_cons,PowerSeries.coeff_zero_eq_constantCoeff,
        map_mul]
      have ha : PowerSeries.constantCoeff (f a) = 0 := by simpa using h a
      rw [ha,zero_mul]

lemma listprod_coeff_congr_of_two {σ : Type*} (l : List σ) (f g : σ → PowerSeries R)
    (j : ℕ) (hl : 2 ≤ l.length)
    (hf₀ : ∀ s, PowerSeries.coeff 0 (f s) = 0)
    (hg₀ : ∀ s, PowerSeries.coeff 0 (g s) = 0)
    (h : ∀ s, AgreeBelow j (f s) (g s)) :
    PowerSeries.coeff j (l.map f).prod = PowerSeries.coeff j (l.map g).prod := by
  cases l with
  | nil => simp at hl
  | cons a l =>
      have hl₀ : l ≠ [] := by intro he; simp [he] at hl
      simp only [List.map_cons,List.prod_cons]
      rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases hp₁ : p.1 = 0
      · simp [hp₁,hf₀,hg₀]
      · by_cases hp₂ : p.2 = 0
        · simp [hp₂,listprod_constant_zero l f hf₀ hl₀,listprod_constant_zero l g hg₀ hl₀]
        · rw [h a p.1 (by omega),agreeBelow_listprod l f g h p.2 (by omega)]

lemma listprod_coeff_mono_of_two {σ : Type*} (l : List σ) (f g : σ → PowerSeries ℝ≥0∞)
    (j : ℕ) (hl : 2 ≤ l.length)
    (hf₀ : ∀ s, PowerSeries.coeff 0 (f s) = 0)
    (hg₀ : ∀ s, PowerSeries.coeff 0 (g s) = 0)
    (h : ∀ s, LeBelow j (f s) (g s)) :
    PowerSeries.coeff j (l.map f).prod ≤ PowerSeries.coeff j (l.map g).prod := by
  cases l with
  | nil => simp at hl
  | cons a l =>
      have hl₀ : l ≠ [] := by intro he; simp [he] at hl
      simp only [List.map_cons,List.prod_cons]
      rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
      apply Finset.sum_le_sum
      intro p hp
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases hp₁ : p.1 = 0
      · simp [hp₁,hf₀,hg₀]
      · by_cases hp₂ : p.2 = 0
        · simp [hp₂,listprod_constant_zero l f hf₀ hl₀,listprod_constant_zero l g hg₀ hl₀]
        · exact mul_le_mul' (h a p.1 (by omega)) (leBelow_listprod l f g h p.2 (by omega))

def factors {σ : Type*} (α : σ →₀ ℕ) : List σ :=
  α.support.toList.flatMap (fun s => List.replicate (α s) s)

lemma factors_length {σ : Type*} (α : σ →₀ ℕ) :
    (factors α).length = α.sum (fun _ n => n) := by
  classical
  simp [factors,List.length_flatMap,Finsupp.sum]

lemma factors_prod {σ : Type*} (α : σ →₀ ℕ) (f : σ → PowerSeries R) :
    ((factors α).map f).prod = α.prod (fun s n => f s^n) := by
  classical
  simp [factors,List.map_flatMap,List.flatMap_def,List.map_map,Finsupp.prod]

lemma factors_prod_fintype {σ : Type*} [Fintype σ] (α : σ →₀ ℕ) (f : σ → PowerSeries R) :
    ((factors α).map f).prod = ∏ s, f s^(α s) := by
  rw [factors_prod,Finsupp.prod_fintype]
  exact fun s => pow_zero _

lemma factors_single {σ : Type*} [DecidableEq σ] (s : σ) :
    factors (Finsupp.single s 1) = [s] := by simp [factors]

end WP.Majorant
