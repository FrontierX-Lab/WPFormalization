import WPFormalization.Statements.ChainDefinitions

/-! Manin--Zograf's classical fixed-genus, large-cusp asymptotic.

Source: Manin--Zograf, Ann. Inst. Fourier 50 (2000), Section 6,
Theorem 6.1, equations (17)--(20), printed pp.528--529 (PDF pp.11--12),
https://www.numdam.org/item/10.5802/aif.1764.pdf .

Their raw volume is the integral of kappa_1^d, d=3g+n-3. Equation (18)
states that rawVolume/(n! d!) is xCritical^(-n) times a fixed power of
n+1 and a positive constant with lower-order corrections. The physical
volume is (2*pi^2)^d rawVolume/d!. Dividing by this project's factorial
normalization leaves (2*xCritical)^(-n) times polynomial factors in n;
taking logarithms yields the weaker estimate below. Constants and cusp
thresholds depend on the fixed genus, including genus zero and one.

Transfer to an arbitrary PsiTheory uses the classical DVV uniqueness,
KMZ finite transform and Wolpert normalization; those identifications are
part of this deferred classical proof. No actual geometric instance, no
genus-uniform estimate and no diagonal-chain profile are supplied here. -/
noncomputable section
namespace WP.External

@[blueprint "ext:fixed-genus"]
theorem fixed_genus_normalized_volume_logarithm (P : PsiTheory) (g : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, Stable g n →
      |Real.log (normalizedVolume P g n)+(n : ℝ)*Real.log (2*xCritical)| ≤
        C*Real.log ((n : ℝ)+1) := by
  sorry

end WP.External
