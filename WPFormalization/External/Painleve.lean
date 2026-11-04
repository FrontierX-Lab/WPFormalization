import WPFormalization.Statements.IntersectionInterface
import WPFormalization.HigherOrder.EndpointFormal

/-! Mature Itzykson--Zuber and zero-instanton Painleve I inputs.

PI-IZ: Itzykson--Zuber, hep-th/9201001, p.39 Eqs.(6.7)--(6.10).
The phi coefficients are the uniquely normalized formal solution with phi_0=-1.
In GIKM's convention they are -2^g u_{g,0}. Transfer to an arbitrary PsiTheory
also uses uniqueness of the classical DVV theory, as in the other external
intersection inputs. These classical identifications are deferred together.

PI-LEADING: Garoufalidis--Its--Kapaev--Marino, arXiv:1002.3634v3, p.2
Eqs.(1.1)--(1.5), and Section2.3, especially (2.35)--(2.37).
Here A=8 sqrt(3)/5, S1=-i*3^(1/4)/(2 sqrt(pi)); pi*i/S1 is the negative
real factor -pi/stokesAmplitude. The asserted limit is only the classical
leading normalization, not the target paper's growing-order Gevrey estimate.

All u coefficients below are the actual rational recurrence defined in
EndpointFormal, which matches GIKM (1.3). No arbitrary coefficient family,
profile estimate, transport equation, uniform remainder or new theorem is
introduced as an external input.
-/
noncomputable section
namespace WP.External
open Filter
open scoped Topology

@[blueprint "ext:iz"]
def phiCoefficient (g : ℕ) : ℝ :=
  -(2 : ℝ)^g*(HigherOrder.zeroInstantonCoefficient g : ℝ)

/- Classical Eq.(6.10), including the fixed IZ/Painleve normalization. -/
@[blueprint "ext:iz"]
theorem itzykson_zuber (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    pure P g (List.replicate (3*g-3) 2) =
      (2 : ℝ)^g*((3*g-3).factorial : ℝ)*phiCoefficient g /
        (((5*g-5 : ℕ) : ℝ)*((5*g-3 : ℕ) : ℝ)) := by
  sorry

@[blueprint "ext:painleve-leading"]
def painleveAction : ℝ := 8*Real.sqrt 3/5

@[blueprint "ext:painleve-leading"]
def stokesAmplitude : ℝ := Real.rpow 3 (1/4 : ℝ)/(2*Real.sqrt Real.pi)

@[blueprint "ext:painleve-leading"]
def normalizedZeroInstanton (g : ℕ) : ℝ :=
  -Real.pi/stokesAmplitude * Real.rpow painleveAction (2*(g : ℝ)-1/2) *
    (HigherOrder.zeroInstantonCoefficient g : ℝ) / Real.Gamma (2*(g : ℝ)-1/2)

/- The relative inverse-genus error is explicitly classical: GIKM (2.39),p.12.
The constant is fixed; it has no truncation-order or WP parameter uniformity. -/
@[blueprint "ext:painleve-leading"]
theorem painleve_leading_error :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, 2 ≤ g₀ ∧ ∀ g ≥ g₀,
      |normalizedZeroInstanton g-1| ≤ C/(g : ℝ) := by
  sorry

/- The classical limit follows from the preceding admitted classical rate. -/
@[blueprint "ext:painleve-leading"]
theorem painleve_leading : Tendsto normalizedZeroInstanton atTop (𝓝 1) := by
  obtain ⟨C,hC,g₀,hg₀,he⟩ := painleve_leading_error
  apply tendsto_sub_nhds_zero_iff.mp
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop g₀] with g hg
  simpa only [Real.norm_eq_abs] using he g hg

end WP.External
