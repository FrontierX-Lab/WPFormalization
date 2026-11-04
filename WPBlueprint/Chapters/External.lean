import WPFormalization.Statements
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "External inputs and verification boundaries" =>

:::source_document "paper-v3"
%%%
title := "Li–Wang, Uniform large-genus asymptotics of Weil–Petersson volumes, v3"
kind := .pdf
pdf := "source/paper.pdf"
%%%
:::

:::group "paper_definitions"
Definitions and conventions
:::

:::group "paper_core"
Paper contributions: must be proved
:::

:::group "external_inputs"
Literature inputs: exact interface audit required
:::

:::group "verification_pending"
Infrastructure/source matches still to verify
:::

These nodes describe external inputs and infrastructure candidates. No Lean axiom or admitted declaration is introduced. Candidate tags mean that exact textbook locators or library matches still require checking.

:::proposition "ext:dvv" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "19", anchor := "ext:dvv", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — String, dilaton and DVV identities.

For stable moduli spaces, pure psi intersections satisfy string, dilaton and DVV with bases \<tau\_0^3\>\_0=1 and \<tau\_1\>\_1=1/24. Negative degrees and dimension-mismatched terms vanish. The full normalized formulas used are (B.1)–(B.2), and the pivot equation in Section 4.2.

Reference and scope: Witten \[81\]; Kontsevich \[51\]; Dijkgraaf–Verlinde–Verlinde \[21\]. Paper PDF pages: 19–21, 69–70.
:::

:::proposition "ext:mixed-transform" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "19", anchor := "ext:mixed-transform", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Mixed kappa to psi transform.

For every stable (g,n) and nonnegative degree tuple of total D at most 3g-3+n, the finite mixed kappa/psi identity is exactly (4.4). It identifies actual intersection brackets, not freely chosen solutions of a recurrence.

Reference and scope: Kaufmann–Manin–Zagier \[48\]; Liu–Xu \[55\]; Manin–Zograf \[58\]; Wolpert \[83\] for \[omega\_WP\]=2pi^2 kappa\_1. Paper PDF pages: 19–20.
:::

:::proposition "ext:one-point" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "53", anchor := "ext:one-point", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — One-point psi integral.

For every integer g\>=1, \<tau\_\{3g-2\}\>\_g=1/(24^g g!).

Reference and scope: Kontsevich \[51\], Witten \[81\]; used in Appendix B and Section 13.1. Paper PDF pages: 53, 71.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::

:::proposition "ext:two-point" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "69", anchor := "ext:two-point", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Published two-point bound.

For g\>=1 and nonnegative d\_1+d\_2=3g-1, C\_g(d\_1,d\_2)\<=C\_g(0,3g-1), in normalization (4.3). This is the imported bound; the all-positive multi-point bound B.1 is proved in this paper.

Reference and scope: Delecroix–Goujard–Zograf–Zorich \[19\], equation (6). Paper PDF pages: 69, 71.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::

:::proposition "ext:kdv" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "31", anchor := "ext:kdv", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Integrated KdV identity.

Kontsevich–Witten free energy satisfies F\_01=F\_00^2/2+F\_0000/12 as a formal identity; derivative and string-flow specialization give (6.6).

Reference and scope: Kontsevich \[51\]; Itzykson–Zuber \[43\]; Mulase–Safnuk \[69\]. Paper PDF pages: 31.
:::

:::proposition "ext:iz" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "36", anchor := "ext:iz", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Itzykson–Zuber endpoint identity.

For integer g\>=2, \<tau\_2^\{3g-3\}\>\_g = 2^g (3g-3)! phi\_g / ((5g-5)(5g-3)), where phi(t)=sum phi\_g t^((1-5g)/2), phi\_0=-1, and phi\_doubleprime/3+phi^2=t.

Reference and scope: Itzykson–Zuber \[43\], equation (6.10), https://arxiv.org/abs/hep-th/9201001. Paper PDF pages: 36–37, 85–86.
:::

:::proposition "ext:painleve-leading" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "37", anchor := "ext:painleve-leading", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Painleve I leading normalization.

For -u\_doubleprime/6+u^2=Z and zero-instanton coefficients u\_\{g,0\}, use action a=8sqrt(3)/5 and Stokes multiplier S\_1=-i 3^(1/4)/(2sqrt(pi)). The large-order normalization is that of (7.15)–(7.17). Branches and conventions must be checked before any Lean external theorem is admitted.

Reference and scope: Joshi–Kitaev \[46\]; Kapaev \[47\]; Garoufalidis–Its–Kapaev–Marino \[27\], Section 2.3; https://arxiv.org/abs/1002.3634. Paper PDF pages: 37, 84–86.
:::

:::proposition "ext:painleve-contour" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "84", anchor := "ext:painleve-contour", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Zero-instanton coefficient contour.

Use only the zero-instanton contour deformation and adjacent tritronquee jump, with fixed inner contour radius and exponentially bounded inner remainder, as explicitly quoted in Appendix C.9. Growing-order Gevrey bounds are derived in C.9, not an external axiom.

Reference and scope: Garoufalidis–Its–Kapaev–Marino \[27\], Section 2.3, equations (2.25), (2.29). Paper PDF pages: 84–85.
:::

:::proposition "ext:painleve-borel" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "84", anchor := "ext:painleve-borel", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Exact Borel representation.

Use the lateral Borel representation for the specified tronquee solutions, local square-root Borel singularity, and weighted tail bounds. Sector, lateral constants and normalization are the ones translated explicitly in C.9; their matching remains a verification item.

Reference and scope: Costin–Costin–Huang \[18\], Theorem 2, Proposition 3(i), Lemma 17(c),(f); https://arxiv.org/abs/1310.5330. Paper PDF pages: 84–85.
:::

:::proposition "ext:fixed-cusps" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "6", anchor := "ext:fixed-cusps", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Fixed-cusp volume and bracket estimates.

At every fixed n, use the Mirzakhani–Zograf expansion with universal unspecified positive leading constant, polynomial correction coefficients, and Theorem 3.2(ii) absolute bracket differences. Do not import the value 1/sqrt(pi). Section 11 additionally uses the known unmarked first correction (11.5) after normalization is established.

Reference and scope: Mirzakhani–Zograf \[66\], Theorems 1.2, 3.2(ii), Remark 1.3; Mirzakhani \[64\], Theorem 3.5. Paper PDF pages: 6, 7, 49–50, 53.
:::

:::proposition "ext:fixed-genus" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "51", anchor := "ext:fixed-genus", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Fixed-genus large-cusp asymptotics.

For each fixed stable genus g, the fixed-genus cusp expansion implies log Z\_\{g,n\}=-n log(2x\_c)+O\_g(log(n+1)) as n tends to infinity; constants may depend on fixed g.

Reference and scope: Manin–Zograf \[58\], Theorem 6.1 / Section 6. Paper PDF pages: 51–52.
:::

:::proposition "ext:nef-teissier" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "53", anchor := "ext:nef-teissier", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Nefness and Khovanskii–Teissier.

Cotangent divisors and logarithmic kappa\_1 are nef on the projective coarse moduli space, after a finite family cover where needed. Mixed intersections of these nef rational divisors satisfy J\_k^2\>=J\_\{k-1\}J\_\{k+1\}. Descent changes all intersections by one positive common factor.

Reference and scope: Keel \[49\], Theorem 0.4; Arbarello–Cornalba \[8\]; Lazarsfeld \[52\], Section 1.6; Boucksom–Favre–Jonsson \[10\], Theorem 2.15. Paper PDF pages: 53.
:::

:::proposition "ext:mir-integration" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "59", anchor := "ext:mir-integration", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Geometric multicurve integration.

Mirzakhani integration for ordered disjoint curves on WP moduli, including label allocations, side-exchange and symmetry factors. The exact specialization for pants is (14.6), for mixed critical cuts (G.6); bounded-boundary comparison is (14.7).

Reference and scope: Mirzakhani \[61,64\]; Shen–Wu \[79\], Lemma 29; Mirzakhani–Petri \[65\], Proposition 4.2. Paper PDF pages: 59, 104–106.
:::

:::proposition "ext:shen-wu" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "9", anchor := "ext:shen-wu", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Shen–Wu vanishing gap mechanism.

The short-pants second-moment vanishing-gap argument applies with adjacent volume limit D\_\{g,n-1\}-\>1; this paper supplies the missing uniform volume input.

Reference and scope: Shen–Wu \[79\], Theorem 1 and Proposition 35. Paper PDF pages: 9, 57.
:::

:::proposition "ext:shen-wu-volumes" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "104", anchor := "ext:shen-wu-volumes", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Critical-scale volume bounds.

For component complexity d\>=1, V\_\{a,b\}\<=C (4pi^2)^(d-1) Gamma(d)/sqrt(d); for n=O(sqrt(g)), the matching parent lower bound in G.1 holds, with constants depending on the fixed cusp-scale bound.

Reference and scope: Shen–Wu \[79\], Lemmas 18–19; Mirzakhani–Zograf \[66\], Lemma 5.1. Paper PDF pages: 104.
:::

:::proposition "ext:minmax" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "62", anchor := "ext:minmax", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Localized pants spectral estimate.

N disjoint two-cusp pants with waist lengths at most L, for sufficiently small L with 6L\<1/4, yield at least N-1 positive discrete eigenvalues at most 6L.

Reference and scope: Hide–Thomas \[41\], Lemma 5.3; form min–max and essential spectrum threshold 1/4. Paper PDF pages: 62.
:::

:::proposition "ext:tight-transform" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "100", anchor := "ext:tight-transform", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Tight boundary transform.

The exact tight-volume transform in the root R=Y/(2pi^2), moments M\_j=(2pi^2)^j X^(j+1)(Y), and shifted times of Section 4 gives (F.1). Normalization conversion is proved in F.1.

Reference and scope: Budd–Zonneveld \[14\], Proposition 12. Paper PDF pages: 100.
:::

:::proposition "ext:tight-integration" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "63", anchor := "ext:tight-integration", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Tight multicurve integration.

Factorial moments of protected tight curves are integrated using tight volumes, with connected-complement side symmetry 2^(-k). Protected cusps cannot be added by ordinary differentiation.

Reference and scope: Budd–Lions \[13\], Proposition 3.2. Paper PDF pages: 63, 102.
:::

:::proposition "ext:tight-geometry" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "102", anchor := "ext:tight-geometry", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Deterministic tight-curve constructions.

The deterministic extension constructions retain each counted tuple, extend bad intersecting configurations to a bounded separating tight multicurve, or add a short tight systole; bounds depend on the fixed scaled length window and tuple size.

Reference and scope: Budd–Lions \[13\], proofs of Propositions 5.2–5.3; use their deterministic constructions, not their Boltzmann probabilistic conclusions. Paper PDF pages: 102–103.
:::

:::proposition "ext:short-filling" (parent := "external_inputs") (tags := "external-known") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "105", anchor := "ext:short-filling", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Short-curve filling constructions.

Fixed length and fixed tuple size give bounded topology, boundary length and multiplicity for filled short configurations. For a single nonsimple primitive curve of length at most L, the filled piece has boundary length at most 2L and area at most 4L.

Reference and scope: Mirzakhani–Petri \[65\], proof of Proposition 4.5; Hide \[37\], Definition 4.10 and Lemma 4.11. Paper PDF pages: 105–106.
:::

:::proposition "ext:collar" (parent := "verification_pending") (tags := "external-candidate") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "59", anchor := "ext:collar", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Hyperbolic collar and packing facts.

Embedded collars for sufficiently short simple curves, a Margulis thick-thin decomposition, area packing, and uniqueness of geodesic representatives on finite-area hyperbolic surfaces with geodesic boundary. Specific uniform applications are proved in G.2 and Section 14.

Reference and scope: Classical hyperbolic geometry; exact textbook theorem locators still to verify. Paper PDF pages: 59, 62, 105.

Lean coverage (R25): the associated interface contains only primitive length
less than 2 arsinh(1) implying simplicity, and disjointness of distinct simple
geodesics below the same strict threshold. The exact textbook locators are
Buser Theorems 4.4.6 and 4.1.6, used on cusped surfaces in Hide--Thomas
arXiv:2209.15568v3, printed pages 1 and 8. The broader Margulis, packing, and
representative statements above are not supplied by this interface; this
aggregate node remains only partially covered.

:::

:::proposition "ext:complex-analysis" (parent := "verification_pending") (tags := "external-candidate") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "17", anchor := "ext:complex-analysis", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Complex analytic infrastructure.

Holomorphic implicit/inverse function theorems, Cauchy coefficient and derivative bounds, Rouche zero counts, order-one-half Hadamard products, Pringsheim and formal Lagrange inversion, plus slit harmonic measure estimates. Each use must eventually be split into precise library statements.

Reference and scope: Standard results; precise external textbook locators for missing components remain unverified. Paper PDF pages: 17–18, 40–42, 67–69, 77, 89–96.
:::

:::proposition "ext:optional-stopping" (parent := "verification_pending") (tags := "external-candidate") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "26", anchor := "ext:optional-stopping", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Bounded optional stopping.

A nonnegative supermartingale stopped at a bounded stopping time has expected terminal value at most its initial expectation; used for excursions of 2^Z, stopped before the initial finite complexity.

Reference and scope: Mathlib `Probability.Martingale.OptionalStopping`, `Submartingale.expected_stoppedValue_mono` applied to the negative supermartingale. The local `bounded_optional_stopping` wrapper covers real supermartingales on probability spaces and natural-time stopping times bounded by a deterministic integer; nonnegativity is unnecessary. Paper PDF pages: 26. The current comparison proof uses the proved finite-rank induction `WP.Analysis.finite_rank_log_lower` and does not require a separate random-process instance.
:::

:::proposition "ext:fourier" (parent := "verification_pending") (tags := "external-candidate") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "18", anchor := "ext:fourier", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Fourier inversion and iid lattice estimates.

Fourier inversion on integer laws, with common exponential moments, uniformly positive mass at 0 and 1, and variances bounded away from zero. The parameter-uniform estimates (2.9) are proved in this paper; no uniform LLT is admitted as external.

Reference and scope: Mathlib Fourier and probability infrastructure; standard inversion theorem exact match pending. Paper PDF pages: 18, 23, 98.
:::

:::proposition "ext:stirling" (parent := "verification_pending") (tags := "external-candidate") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "23", anchor := "ext:stirling", citation := "Proposition external", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition external — Stirling and Gamma infrastructure.

Stirling asymptotics with explicit remainder control, Gamma finite products and Gaussian integrals. Growing-order bounds used here must be proved from appropriate exact formulas, rather than assumed to follow from fixed-order asymptotics.

Reference and scope: Mathlib Analysis.SpecialFunctions.Stirling and Gamma; Binet remainder matching still to verify. Paper PDF pages: 23, 37, 85–86, 96.
:::

