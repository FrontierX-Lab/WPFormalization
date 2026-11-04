import WPFormalization.HigherOrder.BoundaryAffineMoment
import WPFormalization.HigherOrder.JointDiagonalPolynomial
/-! A coordinate projection with genuine zero constants pulls back finite degree strata and their literal data polynomials, preserving total degree. Repeated or omitted coordinates are permitted. This finite operation supports the actual canonical beforeCoordinate path; it assumes no path-independent primitive. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def projectNat {p q : ℕ} (ρ : Fin q → Option (Fin p)) (d : Fin p → ℕ) : Fin q → ℕ :=
  fun i => (ρ i).elim 0 d

def projectPattern {p q : ℕ} (B : ℕ) (ρ : Fin q → Option (Fin p))
    (σ : Fin p → Option (Fin (B + 1))) : Fin q → Option (Fin (B + 1)) :=
  fun i => (ρ i).elim (some ⟨0, by omega⟩) σ

lemma classify_project {p q : ℕ} (B : ℕ) (ρ : Fin q → Option (Fin p)) (d : Fin p → ℕ) :
    classify q B (projectNat ρ d) = projectPattern B ρ (classify p B d) := by
  funext i
  cases hi : ρ i with
  | none => simp [projectNat, projectPattern, hi, classify]
  | some j => simp [projectNat, projectPattern, hi, classify]

def projectPolynomial {p q : ℕ} (ρ : Fin q → Option (Fin p))
    (F : MvPolynomial (Fin q) R) : MvPolynomial (Fin p) R :=
  F.eval₂ MvPolynomial.C (fun i => (ρ i).elim 0 MvPolynomial.X)

lemma projectPolynomial_degree {p q : ℕ} (ρ : Fin q → Option (Fin p))
    (F : MvPolynomial (Fin q) R) : (projectPolynomial ρ F).totalDegree ≤ F.totalDegree := by
  apply linear_mv_substitution_degree
  intro i
  cases hi : ρ i with
  | none => simp [hi]
  | some j => simpa only [hi, Option.elim_some] using variable_degree_le_one (R := R) j

lemma projectPolynomial_eval {p q : ℕ} (ρ : Fin q → Option (Fin p))
    (F : MvPolynomial (Fin q) R) (φ : R →+* ℝ) (d : Fin p → ℕ) :
    MvPolynomial.eval₂ φ (fun i => (d i : ℝ)) (projectPolynomial ρ F) =
      MvPolynomial.eval₂ φ (fun i => (projectNat ρ d i : ℝ)) F := by
  let ψ : MvPolynomial (Fin p) R →+* ℝ := MvPolynomial.eval₂Hom φ (fun i => (d i : ℝ))
  have he := MvPolynomial.eval₂_comp_left ψ MvPolynomial.C
    (fun i => (ρ i).elim 0 MvPolynomial.X) F
  have hc : ψ.comp MvPolynomial.C = φ := by ext x; simp [ψ]
  have hx : (ψ ∘ fun i => (ρ i).elim 0 MvPolynomial.X) =
      (fun i => (projectNat ρ d i : ℝ)) := by
    funext i
    cases hi : ρ i <;> simp [hi, ψ, projectNat]
  change ψ (F.eval₂ MvPolynomial.C _) = _
  simpa only [hc, hx] using he

def projectStratumPolynomial {p q : ℕ} (B : ℕ) (ρ : Fin q → Option (Fin p))
    (F : (Fin q → Option (Fin (B + 1))) → MvPolynomial (Fin q) R)
    (σ : Fin p → Option (Fin (B + 1))) : MvPolynomial (Fin p) R :=
  projectPolynomial ρ (F (projectPattern B ρ σ))

lemma projectStratumPolynomial_degree {p q : ℕ} (B D : ℕ) (ρ : Fin q → Option (Fin p))
    (F : (Fin q → Option (Fin (B + 1))) → MvPolynomial (Fin q) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D)
    (σ : Fin p → Option (Fin (B + 1))) :
    (projectStratumPolynomial B ρ F σ).totalDegree ≤ D :=
  (projectPolynomial_degree _ _).trans (hdegree _)

lemma projectStratumPolynomial_actual_eval {p q : ℕ} (B : ℕ) (ρ : Fin q → Option (Fin p))
    (F : (Fin q → Option (Fin (B + 1))) → MvPolynomial (Fin q) R)
    (φ : R →+* ℝ) (f : (Fin q → ℕ) → ℝ)
    (hactual : ∀ v : Fin q → ℕ,
      f v = MvPolynomial.eval₂ φ (fun i => (v i : ℝ)) (F (classify q B v)))
    (d : Fin p → ℕ) :
    f (projectNat ρ d) = MvPolynomial.eval₂ φ (fun i => (d i : ℝ))
      (projectStratumPolynomial B ρ F (classify p B d)) := by
  rw [hactual, classify_project, projectStratumPolynomial, projectPolynomial_eval]
end WP.HigherOrder.JointBoundary
