import WPFormalization.Statements
import WPBlueprint.Chapters.External
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "01-introduction" =>

# Introduction

Let $`V_{g,n}(L_1,\ldots,L_n)` denote the Weil–Petersson volume of the moduli space of genus-$`g` hyperbolic surfaces with $`n` labeled boundary components of lengths $`L_i`. We use the orbifold convention and put 

$$`V_{g,n}=V_{g,n}(0,\ldots,0),\qquad
 V_{g,n}(\mathbf L)=\frac{1}{(3g-3+n)!}
 \int_{\mathcal M_{g,n}(\mathbf L)}\omega_{\mathrm{WP}}^{3g-3+n}.`

 We assume $`2g-2+n>0`. A boundary component of length zero is a cusp. These volumes are computed by Mirzakhani’s recursion \[61\], are generating functions for intersection numbers on $`\overline{\mathcal M}_{g,n}` \[62\], and control the geometry of random hyperbolic surfaces of large genus \[64\]; see \[84\] for a survey, and \[17\] for a survey comparing Weil–Petersson and Masur–Veech volumes.

Precise asymptotics are known in two limits. For fixed $`n` as $`g\to\infty`, Mirzakhani obtained growth estimates and the limits of the basic volume ratios \[64\], and Mirzakhani and Zograf obtained a complete asymptotic expansion \[66\]. For fixed $`g` as $`n\to\infty`, the form of the asymptotics was predicted by Itzykson (see \[90\] Remark 3). In genus zero, where Zograf had given a recursion for the volumes \[89\], Kaufmann, Manin and Zagier proved this prediction and expressed the exponential growth rate through the first zero of $`J_0` \[48\]. Zograf then expressed the generating function of the volumes in every genus through the Kontsevich–Witten free energy at shifted times \[90\], and Manin and Zograf proved the asymptotics for every fixed genus \[58\] Theorem 6.1.

These two limiting descriptions do not by themselves give a uniform approximation when both parameters grow. By \[66\] Theorem 1.2, the coefficient of $`g^{-i}` in the fixed-$`n` expansion is a polynomial in $`n` of degree $`2i` with leading term $`(-1)^in^{2i}/(i!\,(2\pi^2)^i)`. The expansion is thus effectively a series in $`n^2/g`, whose leading terms sum formally to $`\exp(-n^2/(2\pi^2g))`. Once $`n` is of order $`\sqrt g`, all its terms are of comparable size, so no fixed truncation remains a uniform approximation.

Main results. We prove a single asymptotic expansion of $`V_{g,n}` as $`g\to\infty` that is uniform in $`n\ge0`. Its leading term is explicit and contains no undetermined constant, and its relative remainder is uniform from bounded cusp counts to cusp counts growing arbitrarily fast with the genus. The main consequences are the following.

1. Absolute volumes (Theorem {bpref "thm:intro-absolute"}[1.1] and Corollary {bpref "cor:constant"}[1.2]). The relative error is $`O(1/g)` uniformly in $`n`, and $`O(\mathrm e^{-a\sqrt g})` after truncation at an order proportional to $`\sqrt g`. For fixed $`n` this identifies the constant in the Mirzakhani–Zograf asymptotic formula \[66\] Theorem 1.2 as $`1/\sqrt\pi`, as conjectured by Zograf \[91\].

2. Volume ratios (Theorem {bpref "thm:volume"}[1.3]). The ratios $`V_{g,n}/V_{g-1,n+2}`, $`V_{g,n+1}/(2gV_{g,n})` and $`V_{g,n}^2/(V_{g,n-1}V_{g,n+1})` have explicit limits at every cusp density, with rate $`O(1/g)`. The first limit answers Mirzakhani’s question on the asymptotics of $`V_{g,n}/V_{g-1,n+2}` when $`n` grows with $`g` \[64\] Section 1.4. The third settles the remaining case of a question of Shen and Wu \[79\] Question 3, who asked whether $`V_{g,n}^2/(V_{g,n-1}V_{g,n+1})\to1` as $`g+n\to\infty`.

3. Coefficients and the diagonal chain (Theorems {bpref "thm:coefficient"}[1.4] and {bpref "thm:chain"}[1.5]). We determine the ratios of adjacent coefficients of the one-boundary volume polynomial over all degrees, including degrees that grow with the genus; this answers Mirzakhani’s second question \[64\] Section 1.4. We also determine, to logarithmic precision and including bounded genus, the whole chain $`V_{G,0},V_{G-1,2},\ldots,V_{0,2G}`, about whose behavior she remarked in the same section that little was known.

4. Random surfaces with many cusps (Subsection 1.6). Combined with the vanishing-gap argument of Shen and Wu \[79\], the volume ratios show that the spectral gap tends to zero in probability whenever $`n/\sqrt g\to\infty`; the new range $`n\asymp g` completes the negative answer to their question whether such surfaces have a uniform positive spectral gap \[79\] Question 2. The volume ratios also determine the statistics of short geodesics and of the systole at every density above $`\sqrt g`, and the tight length spectrum for every cusp sequence. At the critical scale $`n\asymp\sqrt g` we identify the full primitive length spectrum; this last result needs only the zero-density case of the volume-ratio limits.

Method. The proof has three ingredients. A one-parameter deformation turns the alternating formula for mixed $`\kappa_1`–$`\psi` intersection numbers into a recursion with nonnegative coefficients. The normalization is fixed at the pure-$`\psi` end of the deformation through Painlevé I, with no resurgence assumption. Finally, a local limit theorem in the number of cusps, valid at both ends of the parameter range, passes from generating functions to individual volumes.

## The cusp-density parameter

All our formulas are expressed through a single real parameter. We first define it and then explain, heuristically, why it is the right parameter; the proofs come later.

The genus-zero relation. Let 

$$`X(y)=\sqrt y\,J_1(2\sqrt y)=y-\frac{y^2}{2}+\frac{y^3}{12}-\cdots,
 \qquad y_0=\frac{j_{0,1}^2}{4},\qquad x_c=X(y_0),`

 where $`j_{0,1}` is the first positive zero of $`J_0`. Since $`X'(y)=J_0(2\sqrt y)`, the function $`X` increases from $`0` to $`x_c` on $`[0,y_0]`; write $`Y(x)` for the inverse function. Consider the normalized cusp generating functions

:::definition "eq:intro-Phi" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:wp-volume")
%%%
source := { document := "paper-v3", spans := #[{ page := "4", anchor := "eq:intro-Phi", citation := "Equation 1.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 1.1 — Normalized cusp generating function.

In the setup and notation of this section, the paper defines or asserts:



$$`\Phi_g(x)=\sum_{n\ge0}\frac{V_{g,n}}{(2\pi^2)^{3g-3+n}}\,\frac{x^n}{n!},`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



with the convention that terms with $`2g-2+n\le0` are omitted. In genus zero, $`\Phi_0''(x)=Y(x)`; this is the classical genus-zero computation (cf. \[48\]; \[58\]), and in our normalization it follows from the string equation (see Step 1 of the proof of Theorem {bpref "thm:pants-poisson"}[14.1]). We call $`x` the cusp weight: it weights each cusp in {bpref "eq:intro-Phi"}[1.1]. The cusp weight $`x` and the parameter $`Y=Y(x)\in[0,y_0)` determine each other, and we use whichever is more convenient.

The parameter functions. For $`0\le Y<y_0`, the entire function 

$$`K_Y(z)=\int_0^1X'\!\Bigl(Y+\frac z2(1-s^2)\Bigr)\,\mathrm ds`

 has only positive simple zeros (Section 2); it is the kernel of the recursion in Section 4. Write its first zero as $`2\Delta(Y)` and put $`T(Y)=Y+\Delta(Y)`. The substitution $`v=T-\Delta s^2` shows that $`T=T(Y)` is the unique root in $`(y_0,\pi^2/4]` of

:::definition "eq:SP1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:bessel")
%%%
source := { document := "paper-v3", spans := #[{ page := "4", anchor := "eq:SP1", citation := "Equation 1.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 1.2 — Stationary root T.

In the setup and notation of this section, the paper defines or asserts:



$$`\int_Y^T\frac{X'(v)}{\sqrt{T-v}}\,\mathrm{d}v=0.`


:::



Finally define

:::definition "eq:SP2" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP1")
%%%
source := { document := "paper-v3", spans := #[{ page := "4", anchor := "eq:SP2", citation := "Equation 1.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 1.3 — Action and cusp density.

In the setup and notation of this section, the paper defines or asserts:



$$`I(Y)=\int_Y^{T(Y)} X'(v)\sqrt{T(Y)-v}\,\mathrm{d}v,
 \qquad
 \lambda(Y)=\frac{2X(Y)\sqrt{\Delta(Y)}}{I(Y)}.`


:::



These definitions will be motivated in the next paragraph. In Section 3 we show that $`I>0` and that $`\lambda` is a strictly increasing bijection from $`[0,y_0)` onto $`[0,\infty)`. At $`Y=0` one has $`\Delta=T=\pi^2/4`, $`I=\pi/4` and $`\lambda=0`; as $`Y\uparrow y_0`, $`\Delta\to0` and $`\lambda\to\infty`.

Why $`\lambda` is the cusp density. Let $`h=2g-1` and $`x=X(Y)`. We shall prove (Proposition {bpref "prop:prefactor"}[7.1]) that, uniformly for $`0\le Y<y_0`, 

$$`\Phi_g'(x)=\frac{\Gamma(h)\,\varpi(Y)}{\pi\,4^g\sqrt{\pi h}}\,
 \bigl(\sqrt2\,I(Y)\bigr)^{-h}\Bigl(1+O\Bigl(\frac{\log g}{g}\Bigr)\Bigr),`

 where $`\varpi` is the explicit positive function in {bpref "eq:intro-varpi"}[1.6] below. Thus the cusp weight changes the exponential growth only through the action $`I(Y)`.

Now regard the terms of the series $`\Phi_g'(x)=\sum_{k\ge0}V_{g,k+1}x^k/((2\pi^2)^{3g-2+k}k!)` as the weights of a probability distribution on the number $`k` of additional cusps. Its mean is $`x\,\mathrm d\log\Phi_g'/\mathrm dx`. Since $`I'(Y)=-X'(Y)\sqrt{\Delta(Y)}` and $`\mathrm dY/\mathrm dx=1/X'(Y)`, the leading term in 1.4 gives 

$$`x\frac{\mathrm d}{\mathrm dx}\log\bigl(\sqrt2\,I(Y)\bigr)^{-h}
 =h\,\frac{X(Y)\sqrt{\Delta(Y)}}{I(Y)}=\frac{h\lambda(Y)}2 .`

 So, under the cusp weight $`x`, the number of additional cusps is about $`h\lambda(Y)/2\approx g\lambda(Y)`. To recover a single volume $`V_{g,n}`, one chooses $`Y` so that the leading approximation to this mean equals $`n-1`, that is, $`\lambda(Y)=2(n-1)/(2g-1)`, and estimates the probability of the value $`k=n-1` by a local limit theorem. In particular $`\lambda(Y)` is, to leading order, the cusp density $`n/g`, and we use $`Y` and $`\lambda` interchangeably. This heuristic produces the leading term in Theorem {bpref "thm:intro-absolute"}[1.1]. As $`n/g` increases from $`0` to $`\infty`, the parameter $`Y` increases from $`0` to $`y_0` and the cusp weight $`x` from $`0` to $`x_c`.

The difficulty is to make this heuristic rigorous with relative errors uniform in $`n`. The proof of 1.4 uses a differential equation in $`Y` whose integration constant is fixed at the endpoint $`Y=y_0`, and the passage from the generating function to its coefficients needs Fourier bounds that survive at both ends of the parameter interval. Subsection 1.7 describes these steps.

A matrix-model interpretation. The cusp weight is a defect weight in Jackiw–Teitelboim (JT) gravity, and $`Y` locates the edge of the corresponding spectral density. At the endpoint $`Y=y_0` the square-root edge becomes cubic. Subsection 15.1 gives the precise dictionary with the defect-deformed matrix model of Maxfield–Turiaci and Witten \[59\]; \[82\]; \[22\]. In this language the endpoint corresponds to the $`(2,3)` critical point, and this is the point at which our normalized recursion reduces to pure $`\psi` intersection numbers. The interpretation does not by itself control the remainders.

## Absolute volumes and Zograf’s constant

For $`n\ge1` put $`h=2g-1` and $`k=n-1`, let $`Y\in[0,y_0)` be the solution of $`\lambda(Y)=2k/h`, and put $`x=X(Y)`. Define

:::definition "eq:intro-leading" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP2, eq:intro-varpi")
%%%
source := { document := "paper-v3", spans := #[{ page := "5", anchor := "eq:intro-leading", citation := "Equation 1.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 1.5 — Explicit absolute-volume model.

In the setup and notation of this section, the paper defines or asserts:



$$`\widehat V_{g,n}=\frac{(2\pi^2)^{3g-3+n}\,\Gamma(h)}{\pi\,4^g\sqrt{\pi h}}\,
 \frac{\varpi(Y)}{(\sqrt2\,I(Y))^{h}}
 \left(\frac{k}{\mathrm e x}\right)^{k}
 \sqrt{\frac{k}{h\,x\Psi'(x)}},`


:::



where $`\Psi(X(y))=\lambda(y)/2` for $`0\le y<y_0`, and $`\varpi(Y)>0` is given by

:::definition "eq:intro-varpi" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "5", anchor := "eq:intro-varpi", citation := "Equation 1.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 1.6 — Absolute prefactor varpi.

In the setup and notation of this section, the paper defines or asserts:



$$`\varpi(Y)^2=\frac{I(Y)}{\Delta(Y)^{3/2}}
 \left(\int_0^1(1-s^2)\,\frac{X(v)}{v}\,\mathrm ds\right)^{-1},
 \qquad v=T(Y)-\Delta(Y)s^2;`


:::



here $`X(v)/v` is an entire function of $`v`, equal to one at $`v=0`. For $`n=0` we put $`\widehat V_{g,0}=\Gamma(2g-2)(4\pi^2)^{2g-3}/\sqrt{\pi g}`.

The formula {bpref "eq:intro-leading"}[1.5] is the heuristic of Subsection 1.1 made explicit. Its first two factors are $`(2\pi^2)^{3g-3+n}` times the approximation 1.4 of $`\Phi_g'(x)`. The coefficient of $`x^k` is about $`\Phi_g'(x)x^{-k}` times the probability of the center of the distribution, and $`k!` times that probability is $`(k/\mathrm e)^k\sqrt{k/(hx\Psi'(x))}` to leading order; here $`hx\Psi'(x)` is the variance scale supplied by the leading action. We use the Poisson point mass $`\mathrm e^{-k}k^k/k!` at the center rather than its Gaussian approximation $`(2\pi k)^{-1/2}`. This choice makes the same formula correct when the cusp count stays bounded, where the number of additional cusps is approximately Poisson rather than Gaussian. At $`k=0` the last two factors in {bpref "eq:intro-leading"}[1.5] are interpreted as their limits, which are one; then $`Y=0`, $`\varpi(0)=1` and $`\widehat V_{g,1}=\Gamma(2g-1)(4\pi^2)^{2g-2}/\sqrt{\pi(g-1/2)}`. The case $`n=0` is reduced to $`n=1` by the dilaton identity {bpref "eq:TL12"}[6.4] at $`p=0` (Section 11).

The correction coefficients $`A_j(g,n)` below, with $`A_0=1`, are determined by finite recursive rules from the kernels together with one-dimensional integrals in $`Y`; see {bpref "eq:CG3"}[10.5] and {bpref "eq:AV7"}[11.7]; the first is written out in {bpref "eq:CG12"}[D.24]. For $`n\ge1` they are analytic functions of the parameter $`Y`, including both endpoints of its interval.

:::theorem "thm:intro-absolute" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-leading, eq:AV7, eq:CG3")
%%%
source := { document := "paper-v3", spans := #[{ page := "5", anchor := "thm:intro-absolute", citation := "Theorem 1.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 1.1 — Uniform absolute expansion.

There are constants $`C,B,c,g_0>0` such that, for every $`g\ge g_0` and every integer $`0\le K\le c\sqrt{2g-1}`, 

$$`\sup_{n\ge0}\left|\frac{V_{g,n}}{\widehat V_{g,n}}
       -\sum_{j=0}^K\frac{A_j(g,n)}{(2g-1)^j}\right|
 \le\frac{CB^{K+1}((K+1)!)^2}{(2g-1)^{K+1}},`

 and the coefficients satisfy $`|A_j(g,n)|\le CB^j(j!)^2` for all $`g\ge g_0` and $`n\ge0`. In particular, 

$$`\sup_{n\ge0}\left|\frac{V_{g,n}}{\widehat V_{g,n}}-1\right|=O(g^{-1}).`

 Taking $`K` to be a sufficiently small fixed multiple of $`\sqrt g`, rounded down to an integer, gives relative error $`O(\mathrm{e}^{-a\sqrt g})` for some $`a>0`, uniformly in $`n`.
:::



The uniformity in $`n` is the main point: Theorem {bpref "thm:intro-absolute"}[1.1] replaces the fixed-$`n` series in $`n^2/g` by an expansion in $`1/g` alone. The same estimate applies when $`n` is fixed, when $`n` is proportional to $`g`, and when $`n/g\to\infty`. In the first regime the saddle is near $`x=0`; as $`n/g\to\infty` it tends to the radius of convergence $`x_c` of the fixed-genus generating functions of Manin and Zograf. In this way a single formula joins the two classical regimes. The order $`g^{-1}` is sharp for this choice of leading term (Theorem {bpref "thm:absolute"}[11.1]); including the first correction {bpref "eq:CG12"}[D.24], or {bpref "eq:AV7"}[11.7] for $`n=0`, gives error $`O(g^{-2})`. The proof is completed in Section 11.

For fixed $`n`, Mirzakhani and Zograf proved that $`V_{g,n}\sim C(2g-3+n)!\,(4\pi^2)^{2g-3+n}/\sqrt g` for a universal constant $`C>0` \[66\] Theorem 1.2. On the basis of numerical data, Zograf had conjectured that $`C=1/\sqrt\pi` \[91\]; see also \[66\] Remark 1.3. The same value appears in physical predictions. Saad, Shenker and Stanford obtained the unmarked large-genus prediction from the JT matrix integral under a resurgence assumption \[77\] Section 5.6. Okuyama and Sakai extracted the constant $`1/\sqrt\pi`, together with first corrections for the coefficients of $`V_{g,1}(L)` at each fixed degree, numerically from the KdV equation \[71\] Section 2.4, equation (89). Kimura conjectured the corresponding asymptotics of $`V_{g,n}(\mathbf L)` from JT gravity \[50\] equation (28), and Eynard, Garcia-Failde, Gregori, Lewański and Schiappa derived it from the nonperturbative topological recursion, assuming that the generating series of Weil–Petersson volumes is resurgent \[25\] Section 6.1, equation (6.7).

Our argument uses no resurgence assumption. We fix the normalization at the endpoint $`Y=y_0` of the parameter interval, where the problem reduces to pure $`\psi` intersection numbers and only the single sequence $`\langle\tau_2^{3g-3}\rangle_g` enters. An identity of Itzykson and Zuber \[43\] expresses this sequence through the formal power-series solution of Painlevé I, whose large-order asymptotics follow from the results of Joshi–Kitaev, Kapaev, and Garoufalidis, Its, Kapaev and Mariño \[46\]; \[47\]; \[27\]. The leading term and the first correction of this sequence also appear as a special case of the uniform asymptotics for $`\psi` intersection numbers announced by Guo, Yang and Zagier \[32\]; we derive both from Painlevé I in Subsections 7.3 and C.9, and use \[32\] only as an independent check. Comparison with the Mirzakhani–Zograf expansion gives the following corollary.

:::corollary "cor:constant" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-Phi")
%%%
source := { document := "paper-v3", spans := #[{ page := "6", anchor := "cor:constant", citation := "Corollary 1.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Corollary 1.2 — Zograf's constant.

For every fixed $`n\ge0`, as $`g\to\infty`, 

$$`V_{g,n}=\frac{(2g-3+n)!\,(4\pi^2)^{2g-3+n}}{\sqrt{\pi g}}
 \bigl(1+O_n(g^{-1})\bigr).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



This is proved at the end of Section 7. Together with the bracket estimate {bpref "eq:TL23"}[6.15], it also gives the formula conjectured by Kimura \[50\] equation (28): for fixed $`n\ge1` and nonnegative lengths $`L_i=o(\sqrt g)`, 

$$`V_{g,n}(\mathbf L)\sim\sqrt{\frac2\pi}\,(4\pi^2)^{2g-3+n}\,\Gamma\Bigl(2g+n-\frac52\Bigr)\prod_{i=1}^n\frac{\sinh(L_i/2)}{L_i/2}.`

 The factors at $`L_i=0` are interpreted by continuity. A direct derivation is given in 7.19 below.

Bounded geodesic boundaries. Proposition {bpref "prop:bounded-boundaries"}[9.4] extends the leading comparison to a fixed number of nonzero boundary lengths in a compact set, uniformly over all cusp counts. Its explicit factor interpolates, as $`n/g` runs from zero to infinity, between the fixed-cusp factor $`\sinh(L/2)/(L/2)` of \[65\] and the fixed-genus, large-cusp factor $`I_0(j_{0,1}L/(2\pi))` of \[40\]. The interpolation is given in {bpref "eq:boundary-profile"}[9.23]; both the number and lengths of the nonzero boundaries remain bounded.

## Volume ratios

For sufficiently large $`g`, define 

$$`B_{g,n}=\frac{V_{g,n}}{V_{g-1,n+2}},\qquad
 C_{g,n}=\frac{V_{g,n+1}}{2gV_{g,n}},\qquad
 D_{g,n}=\frac{V_{g,n}^2}{V_{g,n-1}V_{g,n+1}}.`

 The first two quantities are defined for $`n\ge0`, and the third for $`n\ge1`. For each fixed $`n`, Mirzakhani proved that $`B_{g,n}\to1` and $`C_{g,n}\to4\pi^2` \[64\] Theorem 3.5, and she asked for the asymptotics of $`B_{g,n}` when $`n=n(g)\to\infty` \[64\] Section 1.4. An estimate of Mirzakhani and Zograf states that $`|(2g-2+n)V_{g,n}/V_{g,n+1}-1/(4\pi^2)|\le cn/(2g-2+n)` for stable $`(g,n)` with $`n\ge1` \[66\] Lemma 5.1; together with the fixed-$`n` result, this gives $`C_{g,n}\to4\pi^2` whenever $`n=o(g)`. When $`n` is comparable to or larger than $`g`, the limits depend on the density $`n/g`, through the functions

:::definition "eq:SP3" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP2, def:wp-volume")
%%%
source := { document := "paper-v3", spans := #[{ page := "7", anchor := "eq:SP3", citation := "Equation 1.7", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 1.7 — Volume-ratio profiles.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal B(\lambda(Y))=\frac{\pi^2}{4\Delta(Y)},\qquad
 \mathcal C(\lambda(Y))=\frac{\lambda(Y)\pi^2}{X(Y)}.`


:::



They are well defined because $`\lambda` is a bijection, and they take the continuous values $`\mathcal B(0)=1` and $`\mathcal C(0)=4\pi^2`. Heuristically, $`\mathcal C` appears because $`x\Phi_g''(x)/\Phi_g'(x)` is approximately the mean number $`n-1` of additional cusps, and $`\mathcal B` because $`\Phi_{g-1}'''(x)/\Phi_g'(x)` is approximately $`8\Delta(Y)`; see 6.20 and 6.21.

:::theorem "thm:volume" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3")
%%%
source := { document := "paper-v3", spans := #[{ page := "7", anchor := "thm:volume", citation := "Theorem 1.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 1.3 — Uniform volume ratios.

There are constants $`C_0,g_0>0` such that, for every $`g\ge g_0`, 

$$`\sup_{n\ge0}\left|\frac{B_{g,n}}{\mathcal B(n/g)}-1\right|\le\frac{C_0}{g},
 \qquad
 \sup_{n\ge0}\left|\frac{C_{g,n}}{\mathcal C(n/g)}-1\right|\le\frac{C_0}{g},`

 and 

$$`\sup_{n\ge1}|D_{g,n}-1|\le\frac{C_0}{g}.`

 In particular, along every path $`n/g\to\infty` with $`g\to\infty`, 

$$`B_{g,n}\sim\frac{\pi^2}{3\sqrt5\,j_{0,1}}\sqrt{n/g},\qquad
 C_{g,n}\sim\frac{\pi^2}{x_c}\frac ng.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Section 9 proves the uniform limits directly from a local limit theorem. The inverse-genus error follows from the sharper coefficient estimates, as shown in Section 11.1. Before this theorem, the limit of $`C_{g,n}` was known for $`n=o(g)`, as described above, and the limit $`B_{g,n}\to1` for $`n=o(\sqrt g)`, by the absolute estimate \[66\] Theorem 1.8. Theorem {bpref "thm:volume"}[1.3] removes these restrictions and gives the rate $`O(g^{-1})` uniformly in $`n`.

The statement on $`D_{g,n}` answers a question of Shen and Wu \[79\] Question 3, which asks whether $`D_{g,n}\to1` as $`g+n\to\infty`. As they observe, the answer is affirmative when $`n=o(g)`, by \[66\] Lemma 5.1, and when $`g` is fixed, by \[58\] Theorem 6.1; they also proved $`1/2-\pi^2/20\le\liminf D_{g,n}\le\limsup D_{g,n}\le1` for every cusp sequence \[79\] Proposition 36. Theorem {bpref "thm:volume"}[1.3] supplies the remaining range, in which $`g\to\infty` and $`n/g\not\to0`. Combined with the fixed-genus case, it gives $`D_{g,n}\to1` whenever $`g+n\to\infty`.

## Adjacent coefficients

Mirzakhani’s second question \[64\] Section 1.4 concerns adjacent coefficients when the degree grows with the genus. We write the one-boundary volume polynomial in the normalization of \[64\], 

$$`V_{g,1}(L)=\sum_{k=0}^{N}\frac{a_{g,k}}{(2k+1)!}L^{2k},
 \qquad N=3g-2.`

 The normalized intersection bracket $`b_{g,k}=[\tau_k]_{g,1}` uses the expansion in $`2L`, and hence $`b_{g,k}=4^k a_{g,k}` (Section 4). For fixed $`k`, its adjacent ratio tends to one \[64\] Theorem 3.5; the corresponding ratio $`a_{g,k}/a_{g,k+1}` tends to four. Thus the limit one stated in \[64\] Section 1.4 refers to the bracket normalization, which is also the one used in \[55\].

:::theorem "thm:coefficient" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H5, eq:C1")
%%%
source := { document := "paper-v3", spans := #[{ page := "8", anchor := "thm:coefficient", citation := "Theorem 1.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 1.4 — All adjacent degrees.

For $`0\le k<N`, let $`t_{g,k}\in(0,\pi)` be determined by 

$$`\frac{2k+1}{2g-1}
 =\frac{t_{g,k}^{2}\sin t_{g,k}}
 {\sin t_{g,k}-t_{g,k}\cos t_{g,k}}.`

 Then 

$$`\sup_{0\le k<3g-2}
 \left|\frac{a_{g,k}/a_{g,k+1}}{4\pi^2/t_{g,k}^{2}}-1\right|
 =O(g^{-1/8}).`

 In particular, $`a_{g,k}/a_{g,k+1}\to4` for every $`k=o(g)`, and, with $`m=N-k\ge1`, 

$$`\frac{a_{g,N-m}}{a_{g,N-m+1}}
 \sim\frac{4\pi^2g}{5m}\qquad\text{if }m=o(g).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The density $`(2k+1)/(2g-1)` keeps the exact codimension $`m` in the saddle equation; this is why the last formula also covers bounded positive $`m`. Section 13 proves the uniform equivalent, and Appendix E proves the stated error. On the range $`k\ge\varepsilon g`, for each fixed $`\varepsilon\in(0,3)`, the stronger error $`O_\varepsilon(g^{-1/4})` holds, again including bounded positive codimension.

For each fixed codimension, Liu and Xu obtained a complete expansion of the coefficients relative to the top one \[55\] Theorem 1.2, a partial answer to Mirzakhani’s question. The bounded-codimension case of Theorem {bpref "thm:coefficient"}[1.4] agrees with their result after the change of normalization. What is new is uniformity over all degrees, including degrees and codimensions that grow with the genus.

The trigonometric saddle equation is the stationary equation of an instanton prediction from physics; see Subsections 1.8.2 and 13.7.

## The diagonal chain

Along the chain $`V_{G,0},V_{G-1,2},\ldots,V_{0,2G}` the Euler characteristic is constant, and genus is traded for pairs of cusps. Mirzakhani noted that the adjacent ratios at the two ends of this chain follow from the fixed-$`n` and fixed-$`g` asymptotics, but that little was known about the behavior of the whole sequence \[64\] Section 1.4. Let $`Y(u)` correspond to $`\lambda=2u/(1-u)` and define

:::definition "eq:WC1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "8", anchor := "eq:WC1", citation := "Equation 1.8", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 1.8 — Full diagonal chain rate profile.

In the setup and notation of this section, the paper defines or asserts:



$$`F(t)=\int_0^t\log\frac{4\Delta(Y(u))}{\pi^2}\,\mathrm{d}u
 \quad(0\le t<1),\qquad F(1)=-2\log(2x_c).`


:::



The endpoint value agrees with the limit of the integral.

:::theorem "thm:chain" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3, eq:WC1")
%%%
source := { document := "paper-v3", spans := #[{ page := "8", anchor := "thm:chain", citation := "Theorem 1.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 1.5 — A logarithmic rate for the full chain.

Uniformly over stable $`(g,n)` with $`2g+n\to\infty`, 

$$`\log\frac{V_{g,n}}{(2g+n-3)!(4\pi^2)^{2g+n-3}}
 =\frac{2g+n}{2}F\!\left(\frac n{2g+n}\right)+o(2g+n).`

 Consequently, 

$$`\sup_{0\le j\le G}
 \left|\frac1G\log\frac{V_{G-j,2j}}{V_{G,0}}-F(j/G)\right|\to0.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The second statement determines each entry of the chain up to a factor $`\exp(o(G))`, uniformly in its position and including the planar endpoint $`V_{0,2G}`. Section 12 proves it by summing the logarithms of the cusp ratios $`C_{g,j}` and comparing with the fixed-genus asymptotics at the planar end. When the genus tends to infinity, Theorem {bpref "thm:intro-absolute"}[1.1] gives far more precise information; the point of Theorem {bpref "thm:chain"}[1.5] is that it also covers bounded genus.

## Short geodesics and small eigenvalues

Volume ratios control the geometry of random surfaces through Mirzakhani’s integration formula \[61\], which expresses the expected number of short curves of a given topological type through volumes of the surfaces obtained by cutting along them. Let $`\mathbb P^{\mathrm{WP}}_{g,n}` be the probability measure obtained by normalizing Weil–Petersson volume on $`\mathcal M_{g,n}`, and let $`\Delta_X` be the nonnegative Laplace–Beltrami operator of a surface $`X`. The short geometry changes at the scale $`n\asymp\sqrt g`: for $`n=o(\sqrt g)` the spectral gap is bounded below with high probability \[79\] Theorem 3, whereas above this scale it closes.

:::corollary "cor:spectral" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3")
%%%
source := { document := "paper-v3", spans := #[{ page := "9", anchor := "cor:spectral", citation := "Corollary 1.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Corollary 1.6 — Vanishing spectral gap.

Suppose that $`g\to\infty` and that the integer cusp counts satisfy $`n(g)/\sqrt g\to\infty`. Then, for every $`\varepsilon>0`, 

$$`\mathbb P^{\mathrm{WP}}_{g,n(g)}
 \{X:\Delta_X\text{ has an eigenvalue in }(0,\varepsilon)\}\longrightarrow1.`


:::



This corollary is an application of Shen–Wu’s vanishing-gap argument \[79\] Theorem 1 and Proposition 35 with a stronger volume input. Shen and Wu asked whether a generic surface in $`\mathcal M_{g,n}` has a uniform positive spectral gap when $`n` grows significantly faster than $`\sqrt g` \[79\] Question 2. They proved that it does not for $`\sqrt g\ll n\ll g`, noted that Zograf’s deterministic bound \[88\] gives the same conclusion for $`n/g\to\infty`, and expected that the restriction $`n/g\to0` in their theorem could be removed, which would settle the question. The remaining range is $`n\asymp g`. As Shen and Wu point out, their short-curve argument covers this range once the adjacent-volume limit $`D_{g,n-1}\to1` is known, that is, once their question \[79\] Question 3 has an affirmative answer there. Theorem {bpref "thm:volume"}[1.3] supplies this limit, and Subsection 14.1 applies their argument with this input. Corollary {bpref "cor:spectral"}[1.6] therefore completes the negative answer to \[79\] Question 2.

Short geodesics and the systole. Set $`q_g=n(n-1)/(8g\mathcal C(n/g))\asymp n^2/(g+n)`. For small $`L`, the expected number of geodesics of length at most $`L` that cut off two cusps is asymptotic to $`q_gL^2` (Proposition {bpref "prop:pants-concentration"}[14.2]), so $`q_g^{-1/2}` is the natural length scale of the shortest curves. Under the hypotheses of Corollary {bpref "cor:spectral"}[1.6], and assuming in addition that $`n/g\to\lambda\in[0,\infty]`, Theorem {bpref "thm:pants-poisson"}[14.1] identifies the Poisson process formed by all primitive closed geodesics on this scale, together with the joint law of the systole and the number of cusps it cuts off. With probability tending to one, the shortest geodesics separate off a genus-zero subsurface that contains only cusps. At limiting cusp density $`\lambda`, the curves that cut off $`k` cusps have rescaled intensity $`2w_k(x_\lambda)t\,\mathrm{d}t`, where $`x_\lambda=X(Y_\lambda)` and the weights $`w_k` are given in 14.3. At zero density only curves cutting off two cusps survive in the limit, whereas at positive density every $`k\ge2` has positive intensity.

Many small eigenvalues. Counting disjoint short pairs of pants and applying the localized min–max argument of Hide and Thomas \[41\], Corollary {bpref "cor:many-spectrum"}[14.3] gives a growing number of eigenvalues tending to zero, with an explicit bound on the $`j`th eigenvalue whenever $`j\to\infty` and $`j=o(q_g)`.

The tight length spectrum. The same estimates determine a different part of the length spectrum for every cusp sequence $`n=n(g)\ge0`. A tight geodesic is shortest in its homotopy class after filling all cusps. In Theorem {bpref "thm:tight-spectrum"}[14.4], the primitive tight lengths, multiplied by $`\alpha(n/g)=\sqrt{2r(Y_{n/g})}/\pi`, converge to a Poisson process with intensity 

$$`\frac{\cosh t-1}{t}\,\mathrm dt.`

 This extends the near-critical Boltzmann theorem of Budd and Lions \[13\] to arbitrary prescribed cusp counts, using their tight integration formula and geometric moment argument. The scale satisfies $`\alpha(0)=1` and $`\alpha(\lambda)\asymp\lambda^{-1/4}` as $`\lambda\to\infty`.

The critical scale. At $`n/\sqrt g\to c\in(0,\infty)`, the full ordinary primitive length spectrum has a different limit (Theorem {bpref "thm:critical-cluster"}[14.6]). It is the sum of an independent Poisson background of intensity $`(\cosh t-1)\,\mathrm dt/t` and the complete primitive spectra of two-cusp pairs of pants. Their waist lengths form a Poisson process of intensity $`c^2\sinh(s/2)\,\mathrm ds/(8\pi^2)`. Shen–Wu’s short pants count already exhibits this waist intensity \[79\] Lemmas 28 and 33; the full limit retains the correlations between all lengths in each pair of pants and is not Poisson. Besides the volume bounds of \[66\]; \[79\], this critical limit uses only the zero-density genus-ratio limit $`V_{g,n}/V_{g-1,n+2}\to1` from Theorem {bpref "thm:volume"}[1.3], rather than deducing this two-sided limit from the volume bounds of \[66\]; \[79\]. Its additional content is the joint pants decomposition, including the nonsimple curves.

## Strategy of the proof

The heuristic of Subsection 1.1 has two parts: the approximation 1.4 of $`\Phi_g'`, uniform in the cusp weight, and the passage from $`\Phi_g'` to one of its coefficients. We describe how each part is proved.

Mirzakhani’s volumes are intersection numbers of $`\kappa_1` and $`\psi` classes, and $`\kappa_1` can be expressed through pure $`\psi` intersections \[48\]; \[58\]. The resulting formula {bpref "eq:H5"}[4.4] is an alternating sum over the number of additional $`\psi` insertions, and asymptotics for its terms do not control the cancellation. Our first step replaces it by a recursion with nonnegative coefficients.

1. A positive deformation. Moving along the string flow by a time $`Y` replaces the alternating weights $`-X^{(k)}(0)` by the derivatives $`-X^{(k)}(Y)`; see {bpref "eq:H6"}[4.5]. At $`Y=0` the resulting shifted amplitudes are the Weil–Petersson brackets. After a natural rescaling they become, at $`Y=y_0`, pure $`\psi` intersection numbers with insertions of $`\tau_2`. The Dijkgraaf–Verlinde–Verlinde equations turn into a recursion {bpref "eq:H9"}[4.8] whose coefficients are the Taylor coefficients of $`1/K_Y`, and these are nonnegative for every $`Y` (Section 2). Comparing this recursion with an explicit solvable model, the harmonic model {bpref "eq:H12"}[4.11], gives two-sided bounds that are uniform in $`Y` and in all degrees but lose a factor $`\mathrm e^{O(\sqrt g)}` (Proposition {bpref "prop:harmonic"}[5.1]). This step uses no information about volumes.

2. Ratios, a differential equation and the normalization. For a fixed number of distinguished markings, the dilaton equation expresses the $`Y`-derivative of $`\log\Phi_g^{(p)}(X(Y))` through amplitudes with one more marking, and the KdV equation relates genus $`g` to genus $`g-1` with two more markings. Positivity makes the amplitudes decrease as a degree increases, and this upgrades the coarse bounds of step (i) to relative errors $`O(1/g)` for both ratios (Proposition {bpref "prop:marked-ratios"}[6.2]). Integrating the resulting differential equation in $`Y` gives 1.4 up to a factor independent of $`Y`. This factor is fixed at $`Y=y_0`, where only $`\langle\tau_2^{3g-3}\rangle_g` enters and Painlevé I supplies the asymptotics (Section 7). Iterating the same equations gives all higher corrections, with remainders controlled as the order grows (Section 8, with proofs in Appendix C).

3. From generating functions to coefficients. An expansion of a generating function does not by itself approximate its coefficients. We show that $`\Phi_g^{(p)}` is $`(1/X'(Y(x)))^{2g-2+p}` times a power series with nonnegative coefficients (Lemma {bpref "lem:convolution"}[9.1]). This factorization gives Fourier bounds on the circle $`|z|=x`, and hence a local limit theorem for the cusp count, uniformly from $`x` near $`0` to $`x` near $`x_c` (Proposition {bpref "prop:local-limit"}[9.2]). Near $`x=0` the cusp count is nearly Poisson. A change of variables of the type studied by Temme \[80\] then gives an expansion around the Poisson law that remains regular for bounded cusp counts (Section 10, with proofs in Appendix D). Together these estimates yield Theorem {bpref "thm:intro-absolute"}[1.1] (Section 11).

## Relation to previous work

We group earlier work into three threads: the geometry of moduli spaces and curve counting, the asymptotics of volumes and intersection numbers, and short geodesics and spectra of random hyperbolic surfaces. The last subsection compares the present paper with contemporaneous work on Zograf’s constant.

### Moduli spaces, volumes and curve counting

Weil–Petersson volumes play two roles in this paper: they are generating functions for intersection numbers, and they compute probabilities for random hyperbolic surfaces. Penner developed a combinatorial method for computing these volumes \[72\]. Building on McShane’s identity \[60\], Mirzakhani derived a recursion that computes $`V_{g,n}(\mathbf L)` as a polynomial in the squared boundary lengths \[61\]; its coefficients are intersection numbers of tautological classes on $`\overline{\mathcal M}_{g,n}` \[62\], with the symplectic normalization established by Wolpert \[83\]. Mulase and Safnuk recast the recursion as Virasoro constraints and showed that the generating function of mixed $`\kappa_1`–$`\psi` intersections is a one-parameter solution of the Korteweg–de Vries (KdV) hierarchy \[69\]; Eynard and Orantin identified it with the loop equations of a matrix model \[26\]. The identities expressing mixed $`\kappa_1`–$`\psi` intersections through pure $`\psi` intersections, which are the starting point of Section 4, are due to Kaufmann, Manin and Zagier and to Manin and Zograf \[48\]; \[58\]. Related exact formulas include the tight-volume recursions of Budd and Zonneveld \[14\], the KdV boundary-addition identities and fixed-genus Bessel singularity studied by Johnson \[44\], and the Virasoro-theoretic proof by Xiong and Zhou of the intersection-number and cohomological-field-theory descriptions of topological recursion, including variation of the spectral-curve function \[87\] Theorem 1.1 and Section 5.7. These are exact identities; obtaining uniform remainder estimates from them is a separate analytic problem.

Mirzakhani’s integration formula \[61\] expresses the average number of simple multicurves of a prescribed type in terms of volumes of the surfaces obtained by cutting along them. After division by $`V_{g,n}`, these formulas become expectations under Weil–Petersson probability, so relative volume estimates control geometric probabilities. Mirzakhani used this connection to study random surfaces at large genus \[64\], and Mirzakhani and Petri used joint curve counts to obtain Poisson length statistics for closed surfaces \[65\]. A different curve-counting limit fixes the surface and lets the length bound tend to infinity. Mirzakhani’s counting theorem assigns frequencies to simple-curve topological types in that limit \[63\]. Delecroix, Goujard, Zograf and Zorich related these frequencies to intersection numbers and Masur–Veech volumes \[20\]; Ren obtained the large-genus ratio of separating to nonseparating frequencies with many cusps \[75\]. Those frequencies are topological quantities, whereas the processes studied here count short curves on a random surface as its topology varies.

Masur–Veech volumes are the flat counterpart of Weil–Petersson volumes, and their large-genus theory has developed in parallel. Eskin and Zorich conjectured the large-genus asymptotics of Masur–Veech volumes of strata of Abelian differentials \[23\]; Aggarwal proved them for all strata \[1\], and Chen, Möller, Sauvaget and Zagier expressed these volumes through intersection numbers on the strata and evaluated their large-genus limits \[16\]. Rafi and Zorich recently determined the large-$`n` asymptotics of Masur–Veech volumes of strata of quadratic differentials with many simple poles at fixed genus \[74\].

### Asymptotics of volumes and intersection numbers

The fixed-genus regime was recalled at the beginning of the introduction. Here we discuss large-genus estimates at fixed cusp count, coefficients of growing degree, pure $`\psi` intersection numbers and predictions from physics.

Fixed cusp counts. Grushevsky \[29\] and, for closed surfaces, Schumacher and Trapani \[78\] showed that for fixed $`n` the volumes grow like $`(2g)!` up to factors $`c^g`; see the account in \[64\] Section 1.4. After Mirzakhani’s estimates \[64\], Mirzakhani and Zograf obtained the expansion to every fixed order \[66\] Theorem 1.2. They showed that its coefficients are polynomials in $`n` with coefficients in $`\mathbb Q[\pi^{-2},\pi^2]` and observed numerically that only $`\mathbb Q[\pi^{-2}]` occurs \[66\] Theorem 1.2 and Remark 1.3; their leading term also holds when $`n^2/g\to0` \[66\] Theorem 1.8, and their cusp-ratio estimate has error $`O(n/g)` for $`n\ge1` \[66\] Lemma 5.1. Their first unmarked correction enters 11.5. He, Wu and Xue obtained first-order volume-ratio expansions with error $`O((1+n^2)/g^2)` for $`n=o(\sqrt g)` \[36\] Theorem 4.11. Anantharaman and Monk expanded the volume polynomials at large genus \[4\]. Guillermit sharpened the coefficient bounds and treated boundary lengths of order $`\sqrt g` for fixed $`n` \[30\] Theorems 2, 4, 5 and Remark 3. For fixed $`n`, her order-$`j` bound $`(C_nj)^j` grows more slowly with $`j` than our bound involving $`(j!)^2`; our constants, however, are uniform over all cusp counts. Hide, Macera and Thomas gave bounds explicit in the expansion order, cusp count and degrees \[38\] Theorem 4.2, A1–A4. Their genus must exceed an order-dependent multiple of the cusp count, and the errors grow polynomially in the cusp count or degrees, so these bounds do not yield the relative remainder of Theorem {bpref "thm:intro-absolute"}[1.1] at positive cusp density.

Growing degrees. Wu and Xue established effective upper bounds for normalized intersection numbers when some degrees are large compared with $`\sqrt{2g-2+n}`, together with bounds for volumes with large boundary lengths \[85\]. These bounds control individual coefficients and volumes, whereas the adjacent-ratio asymptotics of Theorem {bpref "thm:coefficient"}[1.4] require relative control across neighboring degrees. A further difficulty is that a bracket may itself be small, so that an additive error polynomial in the degree gives no relative control. We use the Mirzakhani–Zograf bracket-difference estimates near the lowest degrees; the full degree range requires the harmonic comparison and the log-concavity argument of Section 13.

Pure $`\psi` intersection numbers. Motivated by Masur–Veech volumes of quadratic differentials, Delecroix, Goujard, Zograf and Zorich conjectured uniform large-genus asymptotics for pure $`\psi` intersections (Appendix E of the arXiv version of \[20\]). Aggarwal proved them for $`o(\sqrt g)` insertions \[2\], and Guo and Yang gave a different proof for at most $`C\log g` insertions, for every fixed $`C`, based on an explicit formula for the $`n`-point generating series \[31\] Theorem 1. For a fixed number of insertions, Eynard, Garcia-Failde, Giacchetto, Gregori and Lewański obtained resurgent expansions to every fixed order, uniformly in the degrees \[24\] Theorem 3.13.

Our comparison needs only fixed positive upper and lower bounds for the normalized pure-$`\psi` intersections. Appendix B proves these bounds by a scalar induction, adapting the recursion estimates of Guo, Yang and Zagier \[32\] and using the published two-point bound of Delecroix, Goujard, Zograf and Zorich \[19\]. The absolute constant is fixed by the single sequence $`\langle\tau_2^{3g-3}\rangle_g` through the Itzykson–Zuber identity and Painlevé I. To match the expansions at the pure-$`\psi` endpoint when the truncation order grows with $`g`, we use the exact identity \[43\] equation (6.10), the zero-instanton contour formula of Garoufalidis, Its, Kapaev and Mariño \[27\], and the Borel representation of Costin, Costin and Huang \[18\]. Alameddine, Marchal, Nikolaev and Orantin recently solved the direct monodromy problem for the Borel-summed zero-parameter solution of Painlevé I and identified it with the tritronquée solutions \[3\]; we do not need this. Borot, Eynard and Giacchetto use comparison with Painlevé I amplitudes to bound topological-recursion correlators, uniformly in genus and number of markings \[9\] Main Theorem and Section 1.3. Their bounds concern the growth of the correlators themselves, whereas the factorial bounds in Theorem {bpref "thm:intro-absolute"}[1.1] concern the order of the inverse-genus expansion after division by an explicit leading term.

Instanton predictions. Eynard, Garcia-Failde, Gregori, Lewański and Schiappa derived large-genus asymptotics for ordinary Weil–Petersson volumes under a resurgence assumption \[25\]. Griguolo, Papalini, Russo and Seminara predicted the coefficients of ordinary Weil–Petersson volumes from instanton contributions \[28\] Section 3.3, Johnson and Rodrigues wrote down the corresponding one-boundary contour integral \[45\] equation (4.22), and Hatsuda, Matsumoto and Okuyama constructed transseries solutions of the KdV equation that governs the genus expansion of the JT partition function, whose leading nonperturbative sector reproduces the instanton terms \[34\]. After a change of conventions, the denominator of this integral is our harmonic model at $`Y=0`, and its stationary equation is the saddle equation of Theorem {bpref "thm:coefficient"}[1.4] (Subsection 13.7). Unlike the leading factor $`\sinh(L/2)/(L/2)` at bounded boundary length, this integral retains the dependence of the coefficients on their degree up to the top degree. Theorem {bpref "thm:coefficient"}[1.4] establishes the resulting asymptotic formula for the true adjacent coefficient ratios, uniformly over all degrees, from exact intersection identities and estimates; no resurgent expansion is assumed.

### Short geodesics and spectra of random hyperbolic surfaces

For closed surfaces, Mirzakhani established a positive spectral gap with high probability \[64\] Section 4.5. Wu and Xue \[86\] and, independently, Lipnowski and Wright \[54\] raised the lower bound to $`3/16-\varepsilon`. Anantharaman and Monk then obtained $`2/9-\varepsilon`, first in the original version of the first part of their Friedman–Ramanujan series \[5\] Theorem 10.1 and now in a separate article \[7\], and then $`1/4-\varepsilon` \[6\] Theorem 1.6; Hide, Macera and Thomas gave a polynomial rate of approach to $`1/4` \[38\]. These results concern closed surfaces sampled with Weil–Petersson measure. In a different model, uniformly random covers of a fixed surface, Magee, Naud and Puder obtained the relative spectral gap $`3/16-\varepsilon` for covers of a compact surface \[57\]. For covers of a fixed cusped surface, Hide and Magee proved that no new eigenvalues appear below $`1/4-\varepsilon`, and deduced that there are closed surfaces of genus tending to infinity with first eigenvalue tending to $`1/4` \[39\]. Growing cusp counts introduce the separating pants mechanism studied by Shen and Wu \[79\]. See \[68\]; \[73\] for surveys of spectral gaps of random hyperbolic surfaces.

The transition occurs at the scale $`\sqrt g`. Below it, Hide proved \[37\] Theorem 1.3 that for $`n=O(g^\alpha)` with $`0\le\alpha<1/2` there is, with probability tending to one, no nonzero eigenvalue below $`1/4-((2\alpha+1)/4)^2-\varepsilon`. Shen and Wu proved a uniform positive lower bound for the spectral gap throughout the range $`n=o(\sqrt g)` \[79\] Theorem 3, and He, Wu and Xue improved the bound for $`n=O(g^\alpha)` to $`1/4-(6(1-\alpha))^{-2}-\varepsilon`, which tends to $`5/36-\varepsilon` as $`\alpha\to1/2` \[36\] Theorem 1.2. At $`n\asymp\sqrt g`, Shen and Wu’s result \[79\] Theorem 2 describes the small-value distribution of the Cheeger constant, not a limiting law for Laplace eigenvalues. Above this scale the spectral gap vanishes in probability (Corollary {bpref "cor:spectral"}[1.6]), which answers negatively the question of Shen and Wu whether a uniform spectral gap persists when $`n/\sqrt g\to\infty` \[79\] Question 2. This is a statement about the Weil–Petersson distribution: Guo, Hua and Shen construct surfaces with $`n/g` tending to any prescribed positive limit and a uniform spectral gap \[33\].

Poisson limits and small eigenvalues at fixed genus were obtained by Hide and Thomas \[41\]; \[40\]; their recent deterministic linear count of eigenvalues below $`1/4` \[42\] concerns a fixed threshold rather than the vanishing thresholds of Corollary {bpref "cor:many-spectrum"}[14.3]. For closed surfaces the picture is different: Monk proved that, with probability tending to one, a Weil–Petersson random closed surface has $`O(g(\log g)^{-3/4})` eigenvalues below $`1/4` \[67\] Theorem 4. In the range $`\sqrt g\ll n\ll g`, the second-moment volume inputs for our short-curve and small-eigenvalue results already follow from \[79\]; what the uniform volume theorem adds is a single intensity valid across all cusp densities as the genus tends to infinity.

Budd and Lions studied the tight length spectrum in a near-critical Boltzmann model, where the cusp count is random \[13\]. They asked whether their limit persists for other cusp weights and under the fixed-count measures \[13\] Open Question 1.6. Recovering a prescribed count requires a local coefficient estimate, beyond concentration of the random count. Theorem {bpref "thm:tight-spectrum"}[14.4] supplies the fixed-count extension: tight volume estimates and a positive Fourier bound allow coefficient extraction at every cusp density. Corollary {bpref "cor:tight-boltzmann"}[14.5] then treats every subcritical cusp weight, including arbitrary approach to the critical endpoint. The planar separating curves in Theorem {bpref "thm:pants-poisson"}[14.1] instead become contractible after filling the cusps, and lie outside the tight spectrum. In genus zero, Budd and Curien showed that the Weil–Petersson random sphere with $`n+1` cusps, with its metric rescaled by $`n^{-1/4}`, converges to the Brownian sphere \[12\].

### Zograf’s constant and contemporaneous work

The first version of this paper was made public on Zenodo on 16 October 2026 \[53\], at [https://doi.org/10.5281/zenodo.23414478](https://doi.org/10.5281/zenodo.23414478). All numbered results and sections cited in this paragraph refer to Zenodo v1, not to the present numbering. That version already contained the constant $`C=1/\sqrt\pi` (Corollary 1.2 and Section 7), the uniform volume-ratio limits (Theorem 1.1), the diagonal chain (Theorem 1.3), the adjacent-coefficient asymptotics over all degrees with the rate $`O(g^{-1/8})` (Theorems 1.4 and 17.1), the absolute expansion uniform in the cusp count with growing-order remainder bounds (Theorems 14.1–14.2), the vanishing spectral gap and many small eigenvalues (Corollaries 1.5–1.6), and the short-curve processes and the systole (Theorem 19.1).

In contemporaneous work, Liu and Xu \[56\], whose preprint was submitted to arXiv on 24 October 2026, also determine $`C=1/\sqrt\pi`. Their deformation joins the cubic curve $`y=z-4z^3` to the sine curve $`y=\sin(2\pi z)/(2\pi)` while keeping the first positive zero fixed. For each fixed number $`n\ge2` of markings, their uniform-variation theorem \[56\] Theorem 1.1 controls the logarithmic derivative of the normalized volumes uniformly in the curve parameter $`t\in[0,1]` by $`O_n(g^{-1})`. Transport from the cubic endpoint determines the constant \[56\] Corollary 1.2, and their first-correction theorem \[56\] Theorem 1.3 adds the $`1/g` term with an $`O_n(g^{-2})` remainder, uniformly in $`t`.

Our deformation is instead the string flow associated with the cusp weight $`x=X(Y)`. Its amplitudes with a fixed number $`p` of distinguished markings encode the derivatives $`\Phi_g^{(p)}(x)` of the cusp generating function. Both arguments use positivity, descendant recursions, the dilaton and KdV equations, and a Painlevé I normalization, but along different deformation families. In the present paper, Section 7 already determines the constant by specializing to $`p=1` and $`Y=0`, hence to $`V_{g,1}`: uniformity in the total cusp count is not needed for this identification. Its role is the stronger conclusion of an expansion valid for every $`n\ge0`, including $`n` growing with $`g`. This requires the coefficient extraction in Sections 9–10 and Appendix D of the present paper, beyond the estimates for a fixed number of distinguished markings.

## Organization and notation

Organization. The main text proves the volume-ratio and adjacent-coefficient limits and the leading-order estimates. It states the higher-order expansions and the tight and critical spectrum theorems with outlines of their proofs; the supporting arguments and the proofs of these statements are collected in Appendices A–G. The paper has four parts.

1. The positive recursion (Sections 2–5). Section 2 introduces the kernels, Section 3 the density parameter, Section 4 the shifted amplitudes and their positive recursion, and Section 5 compares the recursion with the harmonic model. The special-function facts and the bounds for pure $`\psi` intersections are proved in Appendices A and B.

2. Generating functions (Sections 6–8). Section 6 proves the cusp and genus ratios for a fixed number of markings, Section 7 the leading term and Zograf’s constant, and Section 8 states the higher-order expansion, which is proved in Appendix C.

3. Individual volumes (Sections 9–11). Section 9 proves the local limit theorem and the volume-ratio limits, Section 10 states the sharper extraction theorems proved in Appendix D, and Section 11 proves Theorem {bpref "thm:intro-absolute"}[1.1] and the rate in Theorem {bpref "thm:volume"}[1.3].

4. Applications (Sections 12–14). Section 12 treats the diagonal chain, Section 13 the adjacent coefficients, with the rate proved in Appendix E, and Section 14 the geometry of random surfaces, with the proofs of the tight and critical spectrum theorems in Appendices F and G.

The final section summarizes the picture, explains the matrix-model meaning of the parameter and lists open questions.

Proof guide. The following table lists where the main results are proved and the principal results and methods used in their proofs. References to Sections 2–5 include the supporting Appendices A and B.

Thus all limits, and all geometric applications except the two spectrum theorems proved in Appendices F and G, are proved in the main text using only Appendices A and B. Appendices C–E are needed only for the inverse-genus rates and for the expansions to higher order. They can be read independently of one another: Appendix C after Section 8, Appendix D after Section 10, using Theorem {bpref "thm:full-expansion"}[8.2] only through its statement, and Appendix E after Section 13.

Notation. The following table lists the principal symbols and where they are defined.

The complexity parameter $`h` is specified locally: we use $`h=2g-2+n` for volumes with $`n` boundary components and $`h=2g-2+p` for generating functions with $`p` distinguished markings. In particular, $`h=2g-1` in {bpref "eq:intro-leading"}[1.5], where $`p=1` and the remaining cusps are counted by $`k`. Positive constants $`C`, $`c` may change from line to line, and a subscript, as in $`O_p`, indicates the parameters on which an implied constant depends. A few letters have an additional local meaning, stated where it occurs: $`D` is the degree sum $`|\mathbf d|` in Sections 4 and 7 and in Appendix C; $`h_0=2g-2` is the complexity of a closed surface (Appendices C, F and G); the harmonic coefficients $`A_m(h)` are unrelated to the kernel scalar $`A(Y)` and to the coefficients $`A_j(g,n)`; the Laplacian $`\Delta_X` of a surface $`X` is unrelated to $`\Delta(Y)`; and $`T` is a length window in Section 14.
