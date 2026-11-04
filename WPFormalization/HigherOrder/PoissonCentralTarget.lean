import WPFormalization.HigherOrder.PoissonCoefficientOperator

/-! Exact target for Lemma D.6. These are the prescribed central coefficients,
not an existential replacement family. `PoissonCentralExpansionTarget` has no
inhabitant here; the growing-order expansion and joint analytic coefficient
bounds must be proved before associating the original Blueprint lemma. The
product norm on ℂ × ℂ makes its ball an equal-radius polydisk. -/
noncomputable section
namespace WP.HigherOrder

/-- The coefficient t_{m,j} in the original D.19 polynomial. -/
def poissonCentralInverseCoefficient (m j : ℕ) : ℝ :=
  (poissonCentralPolynomial m).coeff (m-j)

/-- The original differential operator T_j[f] in D.20. -/
def poissonCentralAmplitude (f : ℂ × ℂ → ℂ) (j : ℕ) (ν : ℂ) : ℂ :=
  if j=0 then f (ν,ν) else
    ∑m∈Finset.Icc (j+1) (2*j),
      (poissonCentralInverseCoefficient m j:ℂ)*ν^(m-j)*
        WP.coeff (fun z=>f (ν+z,ν)) m

/-- Full conclusion of D.6, including the growing-order range, complex norms,
positive-order values at zero and the actual operator norm. -/
def PoissonCentralExpansionTarget (f : ℂ × ℂ → ℂ) (R : ℝ) : Prop :=
  ∃ ν₀ C : ℝ, 0 < ν₀ ∧ ν₀ < R ∧ 0 < C ∧
    (∀ (h : ℝ) (k K : ℕ), 0 < h → (k:ℝ)/h ≤ ν₀ → (K:ℝ) ≤ h/2 →
      ‖poissonCoefficientOperator h k (fun u=>f (u,((k:ℝ)/h:ℝ))) -
        ∑j∈Finset.range (K+1),poissonCentralAmplitude f j (((k:ℝ)/h:ℝ):ℂ)/(h:ℂ)^j‖ ≤
          C^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) ∧
    (∀ j, AnalyticOnNhd ℂ (poissonCentralAmplitude f j) (Metric.ball 0 ν₀)) ∧
    (∀ j ν, ‖ν‖ < ν₀ → ‖poissonCentralAmplitude f j ν‖ ≤ C^(j+1)*(j.factorial:ℝ)) ∧
    (∀ j, 1 ≤ j → poissonCentralAmplitude f j 0=0) ∧
    (∀ (h : ℝ) (k : ℕ), 0 < h → (k:ℝ)/h ≤ ν₀ →
      ‖poissonCoefficientOperator h k (fun u=>f (u,((k:ℝ)/h:ℝ)))‖ ≤ C)

@[simp] lemma poissonCentralAmplitude_zero (f : ℂ × ℂ → ℂ) (ν : ℂ) :
    poissonCentralAmplitude f 0 ν=f (ν,ν) := by simp [poissonCentralAmplitude]

lemma poissonCentralAmplitude_at_zero (f : ℂ × ℂ → ℂ) (j : ℕ) (hj : 1 ≤ j) :
    poissonCentralAmplitude f j 0=0 := by
  rw [poissonCentralAmplitude,ite_eq_right (by omega)]
  apply Finset.sum_eq_zero
  intro m hm
  have hmj : j < m := by have ht:=Finset.mem_Icc.mp hm;omega
  simp [show m-j≠0 by omega]

end WP.HigherOrder
