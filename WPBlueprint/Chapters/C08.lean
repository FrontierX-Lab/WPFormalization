import WPFormalization.Statements
import WPBlueprint.Chapters.C07
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "09-extraction" =>

# Extracting a prescribed cusp count

The preceding estimates control generating functions, which sum over cusp counts. We now recover a single coefficient, and hence a volume with a prescribed number of cusps. A positive convolution factor supplies Fourier bounds that turn the real-axis estimates into a local limit theorem. Small cusp weight, the interior, and the critical endpoint require separate estimates, with uniform constants across the three ranges.

Subsection 9.4 proves the qualitative volume-ratio limits using the leading estimates from Sections 6–7. The final subsection extends the argument to bounded geodesic boundaries. The higher-order expansions are needed only for the sharper extraction estimates that follow.

## A positive convolution factor

:::lemma_ "lem:convolution" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-Phi")
%%%
source := { document := "paper-v3", spans := #[{ page := "40", anchor := "lem:convolution", citation := "Lemma 9.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 9.1 — Positive convolution factor.

For each stable marked pair $`(g,p)` with $`p\ge1`, the marked generating function has the exact factorization 

$$`\Phi_g^{(p)}(x)=V(x)^h R_{g,p}(x),\qquad
 V(x)=Y'(x)=1/a(Y(x)),\qquad h=2g-2+p,`

 where $`R_{g,p}` has nonnegative Taylor coefficients and converges for $`0\le x<x_c`.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The point of 9.1 is the following. An approximation of $`\Phi_g^{(p)}` on the real axis alone says nothing about its individual coefficients. The factorization shows that, under the cusp weight $`x`, the number of additional cusps is distributed as the sum of $`h` independent variables with generating function $`V(xz)/V(x)` and one further independent nonnegative integer variable; this gives the Fourier bound 9.2 below, which is what a local limit theorem needs.

:::proof "lem:convolution" (uses := "lem:kernel-positivity, eq:H8, eq:H9, ext:complex-analysis")
The proof uses positivity in the parameter: by Lemma {bpref "lem:kernel-positivity"}[2.2], the functions $`\widehat\vartheta_\ell(Y)=a(Y)[z^\ell]K_Y(z)^{-1}` and $`1/a(Y)` have nonnegative Taylor coefficients in $`Y`. Since this positivity in $`Y` is available for the unrescaled coefficients, we do not use the rescaling by $`r(Y)` of {bpref "eq:H7"}[4.6] here.

Undo the normalization in {bpref "eq:H9"}[4.8] and regard the unrescaled coefficients $`\vartheta_\ell=[z^\ell]K_Y(z)^{-1}` as independent variables. In this convention the bases are $`U_{0,3}=\vartheta_0`, $`U_{1,1}(1)=\vartheta_0/8`, and $`U_{1,1}(0)=\vartheta_1/8`. Induction from these bases shows that every amplitude is a finite polynomial with nonnegative coefficients in the variables $`\vartheta_\ell`; each monomial has total degree $`h`, and weighted degree $`m` when $`\vartheta_\ell` is given weight $`\ell`. A linear recursion term adds one factor $`\vartheta_\ell` to a child of complexity $`h-1`; a separating term adds one to children whose complexities sum to $`h-1`. Thus factoring $`a^{-1}` from each of the $`h` factors $`\vartheta_\ell=a^{-1}\widehat\vartheta_\ell` leaves a positive polynomial in the $`\widehat\vartheta_\ell`.

Finally $`Y(x)` has nonnegative coefficients and $`Y(0)=0`. To justify the product used here, a nonzero zero $`y` of $`X` gives $`u(s)=J_1(2\sqrt y\,s)`, with $`u(1)=0` and regular behavior at zero. Integration of $`(s u')'+(4ys-1/s)u=0` against its conjugate gives $`4y\int_0^1s|u|^2\,\mathrm{d}s=\int_0^1(s|u'|^2+|u|^2/s)\,\mathrm{d}s>0`. Thus all nonzero zeros are positive real. Since $`X` has order one half and a simple zero at zero with derivative one, its Hadamard product is $`X(Y)=Y\prod_k(1-Y/\beta_k)`, $`\beta_k>0`. Lagrange inversion now gives 

$$`[x^k]Y(x)=\frac1k[Y^{k-1}](Y/X(Y))^k>0.`

 The inverse series has radius exactly $`x_c`: a smaller radius would, by positivity and Pringsheim’s theorem, give a positive real singularity before $`x_c`, contradicting the analytic real inverse there; the quadratic critical point at $`x_c` supplies the opposite inequality. Composition therefore preserves coefficient positivity and converges for $`0\le x<x_c`, since $`Y(x)<y_0`. Finally, by {bpref "eq:H8"}[4.7], $`\Phi_g^{(p)}(x)=U^{Y}_{g,p}(0^p)` with $`Y=Y(x)`, and the factor $`a(Y)^{-h}` removed above equals $`V(x)^h`. This proves 9.1.
:::



For the coefficient probability law with generating function $`\Phi_g^{(p)}(xz)/\Phi_g^{(p)}(x)`, positivity in 9.1 gives 

$$`\left|\frac{\Phi_g^{(p)}(x\mathrm{e}^{i\theta})}{\Phi_g^{(p)}(x)}\right|
 \le\left|\frac{V(x\mathrm{e}^{i\theta})}{V(x)}\right|^h.`

 This is the Fourier estimate that prevents a generating-function ratio from concealing different local coefficient behavior.

## Mean, variance and a central limit theorem

We first compute the mean and variance of the cusp count under the cusp weight $`x`, and show that it is asymptotically Gaussian; the next subsection upgrades this to a local limit theorem. Recall $`\mathscr D=x\,\mathrm{d}/\mathrm{d}x` and the function $`\Psi` of Lemma {bpref "lem:parameter"}[3.1]. For convenience we repeat its endpoint expansions 3.5, together with that of $`V=1/a(Y(x))`, which follows from $`a(Y)=1-Y+O(Y^2)` and $`Y(x)=x+O(x^2)`: 

$$`\begin{aligned}
 x\downarrow0:\quad& V(x)=1+x+O(x^2),\quad \Psi(x)=2x+O(x^2),\\
 &\mathscr D\Psi(x)=2x+O(x^2),\quad \mathscr D^2\Psi(x)=2x+O(x^2);\\[1mm]
 x\uparrow x_c:\quad&\Psi(x)=\frac5{4\varepsilon}(1+O(\sqrt\varepsilon)),\\
 &\mathscr D\Psi(x)=\frac5{4\varepsilon^2}(1+O(\sqrt\varepsilon)),\quad
 \mathscr D^2\Psi(x)=O(\varepsilon^{-3}),
 \qquad\varepsilon=1-x/x_c.
 \end{aligned}`

 On compact subintervals of $`(0,x_c)`, all needed derivatives are bounded and $`\mathscr D\Psi` is bounded away from zero.

For $`F=\Phi_g^{(p)}` at a positive cusp weight $`x`, let

:::definition "eq:TL37" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:intro-Phi, eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "41", anchor := "eq:TL37", citation := "Equation 9.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 9.4 — Cusp-count law and model center and variance.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathbb P_x(N=k)=\frac{[z^k]F(z)x^k}{F(x)},\qquad
 \mu=h\Psi(x),\qquad \sigma^2=h\mathscr D\Psi(x).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The last two quantities are model center and variance, not claims about their exact finite-genus values. Suppose $`h\to\infty` and $`\mu\to\infty`. For every fixed real $`u`, integrating 6.20 gives 

$$`\log\mathbb E_x \mathrm{e}^{u(N-\mu)/\sigma}
 =\int_0^{u/\sigma}
 \{h\Psi(x\mathrm{e}^s)-h\Psi(x)+O_p(\Psi(x\mathrm{e}^s))\}\,\mathrm{d}s.`

 The interval of integration stays inside $`(0,x_c)`. Expanding $`h\Psi(x\mathrm e^s)-h\Psi(x)=sh\mathscr D\Psi(x)+O(s^2h\mathscr D^2\Psi)`, the first part of the integral is $`u^2/2` plus a Taylor remainder, and the second part is an integrated error; both are $`o(1)`. More precisely, in the critical regime its Taylor remainder and integrated error are $`O_u(h^{-1/2})`; on an interior compact interval they are also $`O_u(h^{-1/2})`. At $`x\to0`, $`\sigma^2\sim\mu`, the Taylor remainder is $`O_u(\mu^{-1/2})` and the integrated error is $`O_u(x/\sqrt\mu)=O_u(\sqrt\mu/h)=o(1)`. These assertions follow directly from 9.3; no estimate for the derivative of the error in 6.20 is required.

Thus the real moment generating functions converge to $`\exp(u^2/2)` along every such sequence. Exponential Markov bounds give tightness; bounds at slightly larger real arguments give uniform integrability along weakly convergent subsequences. Their limiting moment generating functions identify the standard Gaussian. Therefore 

$$`(N-\mu)/\sigma\Longrightarrow\mathcal N(0,1).`



## Fourier bounds and the local limit theorem

A central limit theorem alone does not determine ratios of individual coefficients. We now prove the corresponding local limit theorem.

:::proposition "prop:local-limit" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-Phi, eq:SP2, eq:TL37")
%%%
source := { document := "paper-v3", spans := #[{ page := "41", anchor := "prop:local-limit", citation := "Proposition 9.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 9.2 — Uniform local limit theorem.

Fix $`p\ge1` and use the notation {bpref "eq:TL37"}[9.4]. Along every sequence with $`h\to\infty`, $`\mu\to\infty` and $`x\in(0,x_c)`, 

$$`\mathbb P_x(N=k)=\frac{1+o(1)}{\sqrt{2\pi}\sigma}
 \mathrm{e}^{-u^2/2}\qquad\text{whenever }(k-\mu)/\sigma\longrightarrow u.`

 No relation between $`h` and the distance from $`x` to $`x_c` is required.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "prop:local-limit" (uses := "lem:convolution, prop:marked-ratios, lem:parameter")
Passing to a subsequence, we may assume that $`x` tends to zero, to an interior point, or to $`x_c`. In each case we bound the characteristic function of $`(N-\mu)/\sigma` by an integrable function, uniformly along the sequence; Fourier inversion and the pointwise convergence implied by 9.6 then give 9.7.

On a compact subinterval of $`(0,x_c)`, the coefficient probabilities at zero and one of $`V(xz)/V(x)` have positive uniform lower bounds. If these probabilities are $`p_0,p_1`, then 

$$`\left|\sum_jp_j\mathrm{e}^{ij\theta}\right|^2
 \le1-2p_0p_1(1-\cos\theta).`

 Equations 9.2 and 9.8 give an upper bound $`\exp(-c h\theta^2)` on $`[-\pi,\pi]`. Since $`\sigma` is comparable to $`\sqrt h`, this is integrable Gaussian domination on the rescaled Fourier axis.

At $`x\to0`, one has $`p_0\asymp1`, $`p_1\asymp x`. The same argument gives $`\exp(-c h x\theta^2)`. Since $`hx\asymp\mu` and $`\sigma^2\sim\mu\to\infty`, it again gives integrable domination after rescaling.

Near the critical point a different bound is needed, because the law with generating function $`V(xz)/V(x)` then has variance of order $`\varepsilon^{-2}` and its probabilities at zero and one tend to zero. Quadratic analytic inversion at $`x_c` gives 

$$`V(z)=A_0(1-z/x_c)^{-1/2}
 \Xi\bigl(\sqrt{1-z/x_c}\bigr),\qquad
 A_0>0,\quad \Xi(0)=1,`

 where $`\Xi` is analytic and nonzero near zero and has real coefficients. Put $`\Lambda(w)=\log \Xi(\sqrt w)` and $`w(\theta)=1-(1-\varepsilon)\mathrm{e}^{i\theta}`. Then 

$$`\log\left|\frac{V(x\mathrm{e}^{i\theta})}{V(x)}\right|
 =-\frac14\log\left(1+
 \frac{2(1-\varepsilon)(1-\cos\theta)}{\varepsilon^2}\right)
 +\Re \Lambda(w(\theta))-\Lambda(\varepsilon).`

 There are fixed $`\delta,\varepsilon_0>0` such that 

$$`\left|\frac{V(x\mathrm{e}^{i\theta})}{V(x)}\right|
 \le(1+\theta^2/(4\varepsilon^2))^{-1/8}
 \quad(|\theta|\le\delta,\ 0<\varepsilon\le\varepsilon_0).`

 Indeed, for $`|\theta|\le\varepsilon`, the first derivative at zero of the real part of $`\Lambda(w(\theta))` vanishes, while its second derivative is $`O(\varepsilon^{-3/2})`. Its change is therefore $`O(\theta^2\varepsilon^{-3/2})`, absorbed by half of the leading logarithm in 9.10 when $`\varepsilon` is small. For $`\varepsilon\le|\theta|\le\delta`, its change is bounded by $`C\sqrt\delta`, while the logarithm is at least $`\log(5/4)`. Choose $`\delta` small enough for the same absorption. We used the elementary bound $`2(1-\varepsilon)(1-\cos\theta)\ge\theta^2/4` on the small arc.

On the outer arc $`\delta\le|\theta|\le\pi`, 

$$`|V(x\mathrm{e}^{i\theta})/V(x)|\le C_\delta\sqrt\varepsilon.`

 To see that $`V` is analytic there, note that nonnegative coefficients and $`Y(x)\to y_0` give absolute convergence of $`Y` on $`|x|\le x_c`. Its first two coefficients are positive, so strict triangle inequality gives $`|Y(x_c \mathrm{e}^{i\theta})|<y_0` away from $`\theta=0`. By Lemma {bpref "lem:kernel-zeros"}[2.1], $`X'` has no zero in $`|Y|<y_0`. The inverse-function theorem extends $`Y,V` across the outer arc, where $`V` is uniformly bounded. Since 9.9 gives $`V(x)\asymp\varepsilon^{-1/2}`, 9.12 follows.

On the critical Fourier scale $`\theta=\varepsilon t/\sqrt h`, 9.2 and 9.11 are bounded by 

$$`(1+t^2/(4h))^{-h/8}\le(1+t^2/64)^{-2},\qquad h\ge16.`

 The inequality follows because $`(1+a/h)^h` increases with $`h`. The right side is integrable. The outer contribution after multiplication by $`\sqrt h/\varepsilon` is at most 

$$`2\pi\sqrt h\,C_\delta^h\varepsilon^{h/2-1}\longrightarrow0.`

 This convergence is uniform for arbitrarily small $`\varepsilon`: fix sufficiently small $`\varepsilon_0` with $`C_\delta\sqrt{\varepsilon_0}<1`, and bound 9.14 by $`2\pi\varepsilon_0^{-1}\sqrt h(C_\delta\sqrt{\varepsilon_0})^h` for $`h\ge2`.

These integrable bounds, in the three regimes, complete the proof.
:::



The same Fourier bounds give an upper bound for every point mass, not only near the center. We record it for later use in Section 14 and Appendix F.

:::lemma_ "lem:point-mass" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-Phi")
%%%
source := { document := "paper-v3", spans := #[{ page := "43", anchor := "lem:point-mass", citation := "Lemma 9.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 9.3 — Uniform point-mass bound.

For every $`c_0>0` there is a constant $`C` with the following property. Let $`x\in(0,x_c)`, let $`h,h'` be positive integers with $`h'\ge\max(16,c_0h)`, and let $`G(z)=V(z)^{h'}R(z)`, where $`R` has nonnegative Taylor coefficients, converges for $`|z|<x_c` and satisfies $`R(x)>0`. Then, with $`\sigma^2=h\mathscr D\Psi(x)`, 

$$`\sup_{j\ge0}\frac{[z^j]G(z)\,x^j}{G(x)}\le\frac C\sigma.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:point-mass" (uses := "lem:convolution, lem:parameter")
By Fourier inversion and positivity of the coefficients of $`R`, 

$$`\frac{[z^j]G(z)\,x^j}{G(x)}
 \le\frac1{2\pi}\int_{-\pi}^{\pi}
       \left|\frac{V(x\mathrm e^{i\theta})}{V(x)}\right|^{h'}\mathrm d\theta.`

 On a compact subinterval of $`(0,x_c)`, 9.8 bounds the integrand by $`\mathrm e^{-ch'\theta^2}`, so the integral is $`O(h^{-1/2})`, while $`\sigma\asymp\sqrt h`. Near zero the same argument with $`p_1\asymp x` gives $`\mathrm e^{-ch'x\theta^2}` and the bound $`O((hx)^{-1/2})`, while $`\sigma^2\asymp hx`. Near $`x_c`, put $`\theta=\varepsilon t/\sqrt{h'}` on $`|\theta|\le\delta`; 9.11 and the argument of 9.13 bound this part by $`(\varepsilon/\sqrt{h'})\int(1+t^2/64)^{-2}\,\mathrm dt`. On the outer arc 9.12 gives at most $`2\pi(C_\delta\sqrt\varepsilon)^{h'}\le C\varepsilon h^{-1/2}` once $`C_\delta\sqrt{\varepsilon_0}<1`. Since $`\sigma\asymp\sqrt h/\varepsilon` there, all three regimes give $`O(1/\sigma)`.
:::



## Ratios at a prescribed number of cusps

We now prove the limits in Theorem {bpref "thm:volume"}[1.3]. Each volume ratio is a ratio of coefficients, at the same index, of two marked generating functions. We evaluate both at the same cusp weight, chosen so that the index is, up to a negligible shift, the model center of both. The local limit theorem 9.7 shows that the two local probabilities are asymptotically equal, so the coefficient ratio is asymptotic to the ratio of the generating functions themselves, which Section 6 determines.

:::proof "thm:volume" (uses := "thm:sharp-extraction, lem:parameter, ext:fixed-cusps")
First suppose $`g,n\to\infty`. Put 

$$`k=n-1,\qquad h=2g-1,
 \qquad h\Psi(x)=k.`

 The last equation has a unique solution in $`(0,x_c)` by 6.22 and the parameter bijection. The two families $`\Phi_g'` and $`\Phi_{g-1}'''` have exactly the same complexity $`h`, model center, and model variance. Thus their two local probabilities in 9.7, at the common coefficient index $`k`, have ratio tending to one. Equations 6.21 and 9.7 give 

$$`\frac{[x^k]\Phi_{g-1}'''(x)}{[x^k]\Phi_g'(x)}
 =4r(Y)(1+o(1)).`

 By the definition {bpref "eq:intro-Phi"}[1.1], the coefficients are 

$$`\Phi_g'(x)=
 \frac{V_{g,n}}{(2\pi^2)^{3g-3+n}k!},\qquad
 [x^k]\Phi_{g-1}'''(x)=
 \frac{V_{g-1,n+2}}{(2\pi^2)^{3g-4+n}k!}.`

 Consequently 

$$`B_{g,n}=\frac{\pi^2}{2r(Y)}(1+o(1))
 =\mathcal B\left(\frac{2(n-1)}{2g-1}\right)(1+o(1)).`

 The factorial $`k!` cancels, and the powers of $`2\pi^2` differ by exactly one; this explains the factor in 9.18.

For the cusp ratio, compare $`\Phi_g''` with $`\Phi_g'` at the same index $`k` and the same cusp weight 9.15. Their complexities are $`h+1` and $`h`. Their centers differ by $`\Psi(x)`, and their variances have ratio $`(h+1)/h`. Moreover 

$$`\frac{\Psi(x)}{\sqrt{h\mathscr D\Psi(x)}}=O(h^{-1/2})`

 uniformly in $`x`, because $`\Psi^2/(\mathscr D\Psi)` is continuous in the interior and has finite endpoint limits zero and $`5/4`, respectively. Thus the local probability ratio again tends to one. Undoing {bpref "eq:TL24"}[6.16], 

$$`C_{g,n}=\frac{\pi^2}{g}
 \frac{[x^k]\Phi_g''}{[x^k]\Phi_g'}
 =\frac{\pi^2}{g}\frac{h}{Aar}(1+o(1))
 =\frac{\pi^2(n-1)}{gx}(1+o(1)).`

 Here, as in 9.17, the coefficients $`[x^k]\Phi_g''` and $`[x^k]\Phi_g'` carry the normalizing powers $`(2\pi^2)^{3g-2+n}` and $`(2\pi^2)^{3g-3+n}`; division by $`2g` gives the factor $`\pi^2/g`. With $`\lambda_{\mathrm{eff}}=2(n-1)/(2g-1)`, the last expression equals 

$$`\left(1-\frac1{2g}\right)\mathcal C(\lambda_{\rm eff})(1+o(1)).`



One may replace $`\lambda_{\mathrm{eff}}` by $`n/g` in both 9.18 and 9.21. At a zero limiting slope, use the continuous values $`\mathcal B(0)=1` and $`\mathcal C(0)=4\pi^2` of {bpref "eq:SP3"}[1.7]; at a finite positive slope use continuity; and at an infinite slope use the endpoint equivalents 3.4 of Lemma {bpref "lem:parameter"}[3.1]. Since $`\lambda_{\mathrm{eff}}/(n/g)\to1` whenever $`n\to\infty`, these give the desired relative replacement in all cases.

Finally the exact identity 

$$`D_{g,n}=C_{g,n-1}/C_{g,n}`

 and the adjacent continuity of the profile $`\mathcal C` give $`D_{g,n}\to1` for every growing-cusp sequence. For bounded cusp counts, the classical fixed-cusp theorems give $`B_{g,n}\to1`, $`C_{g,n}\to4\pi^2`, and hence $`D_{g,n}\to1`; these are the only bounded-cusp inputs used here.

If any supremum in Theorem {bpref "thm:volume"}[1.3] did not tend to zero, select a violating sequence of cusp counts. A subsequence either has a fixed bounded cusp count or tends to infinity. The preceding conclusions contradict a fixed violation in both cases. This proves the uniform convergence assertions. Section 11.1 supplies the stated inverse-genus rate using the sharper extraction theorem.
:::



## Bounded geodesic boundaries

The positive factor also permits a fixed number of cusps to be replaced by geodesic boundaries. The resulting factor depends on the cusp density and joins the familiar large-genus and large-cusp boundary profiles. For $`0\le Y\le y_0` and $`L\ge0`, put

:::definition "eq:boundary-profile" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:SP1")
%%%
source := { document := "paper-v3", spans := #[{ page := "7", anchor := "eq:boundary-profile", citation := "Equation 9.23", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 9.23 — Boundary insertion interpolation factor.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathfrak b_Y(L)=\int_0^1
 I_0\!\left(\frac L\pi\sqrt{T(Y)-\Delta(Y)s^2}\right)\,\mathrm ds,`


:::



where $`I_0` is the modified Bessel function of order zero, $`T=Y+\Delta` and $`r=2\Delta`. At $`Y=y_0` use $`T=y_0` and $`\Delta=0`. Writing $`Y_\lambda` for the inverse of $`\lambda(Y)`, we have $`Y_0=0` and $`Y_\infty=y_0`.

:::proposition "prop:bounded-boundaries" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-Phi, eq:boundary-profile")
%%%
source := { document := "paper-v3", spans := #[{ page := "44", anchor := "prop:bounded-boundaries", citation := "Proposition 9.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 9.4 — Boundary lengths at arbitrary cusp density.

Fix an integer $`p\ge1` and $`L_0<\infty`. As $`g\to\infty`, 

$$`\sup_{\substack{n\ge p\\\mathbf L\in[0,L_0]^p}}
 \left|
 \frac{V_{g,n}(L_1,\ldots,L_p,0^{n-p})}
 {V_{g,n}\prod_{i=1}^p\mathfrak b_{Y_{n/g}}(L_i)}-1
 \right|\longrightarrow0.`

 The endpoint factors are 

$$`\mathfrak b_0(L)=\frac{\sinh(L/2)}{L/2},\qquad
 \mathfrak b_{y_0}(L)=I_0\!\left(\frac{j_{0,1}L}{2\pi}\right),`

 with value one at $`L=0`.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The first factor occurs in the fixed-cusp estimate of Mirzakhani and Petri \[65\] Proposition 3.1; the second is the fixed-genus, large-cusp factor of Hide and Thomas \[40\] Theorem 1.5. Here the genus tends to infinity and the cusp count is unrestricted. The number and lengths of the nonzero boundaries remain bounded. For comparison, Budd and Lions obtain a boundary factor for tight volumes with a random cusp count in a near-critical regime \[13\] Proposition 4.2. Exact transformations between ordinary and tight boundary generating functions were established in \[14\].

:::proof "prop:bounded-boundaries" (uses := "prop:local-limit, eq:TL23, eq:H8, ext:fixed-cusps")
Put $`h=2g-2+p`, $`F(x)=\Phi_g^{(p)}(x)` and 

$$`G(x;\mathbf L)=\sum_{k\ge0}
 \frac{V_{g,p+k}(\mathbf L,0^k)}{(2\pi^2)^{3g-3+p+k}}
 \frac{x^k}{k!}.`

 We first compare $`G` with $`F` on the real axis, and then show that the same comparison holds for their coefficients at the saddle.

The boundary insertion. Use the string flow of {bpref "eq:H8"}[4.7], holding its parameter $`Y` fixed while differentiating the KW times. Its linear part gives 

$$`\partial_{t_d}=\sum_{b=0}^d\frac{Y^{d-b}}{(d-b)!}\partial_{t_b'}.`

 For $`g\ge2` the free energy is invariant under the flow. Apply the displayed identity to each external insertion before setting $`x=X(Y)`. In the volume normalization of {bpref "eq:H5"}[4.4], an external degree $`d` has coefficient $`(L^2/(4\pi^2))^d/d!` times the unweighted derivative. Consequently, with $`t_i=L_i^2/(4\pi^2)`, the exact identity is 

$$`\frac{G(X(Y);\mathbf L)}{F(X(Y))}
 =\sum_{\mathbf a,\mathbf b\ge0}c_{g,p}(\mathbf b;Y)
 \prod_{i=1}^p
 \frac{t_i^{a_i+b_i}Y^{a_i}r^{b_i}}
 {a_i!(a_i+b_i)!(2b_i+1)!!}.`

 Indeed, {bpref "eq:TL9"}[6.1] gives $`U^Y_{g,p}(\mathbf b)/U^Y_{g,p}(\mathbf0)=r^{|\mathbf b|}c_{g,p}(\mathbf b;Y)`. Terms with invalid $`\mathbf b` are zero; there is no bound on $`\mathbf a`.

The identity 

$$`\int_0^1(1-s^2)^b\,\mathrm ds=\frac{2^b b!}{(2b+1)!!}`

 and the series for $`I_0` show that replacing $`c_{g,p}` by one in 9.26 gives $`\prod_i\mathfrak b_Y(L_i)`. The same double series with an extra factor $`|\mathbf b|(|\mathbf b|+1)` is bounded uniformly for $`Y\in[0,y_0]` and $`\mathbf L\in[0,L_0]^p`: the inequality $`(a+b)!\ge a!b!` supplies a summable factorial majorant for every fixed polynomial moment. Thus {bpref "eq:TL23"}[6.15], including its one-marking case, gives 

$$`\frac{G(X(Y);\mathbf L)}{F(X(Y))}
 =\prod_i\mathfrak b_Y(L_i)\bigl(1+O_{p,L_0}(g^{-1})\bigr).`

 All terms in 9.26 are nonnegative. The majorant also justifies convergence of the formal string-flow identity for $`0\le x<x_c`. The factors $`\mathfrak b_Y(L)` are at least one; they and their first $`Y` derivatives are uniformly bounded on the compact set under consideration.

Extraction at a prescribed cusp count. The proof of 9.1 applies to every external degree tuple: $`a(Y)^hU^Y_{g,p}(\mathbf b)` has nonnegative Taylor coefficients in $`Y`. Before division by $`F`, the insertion identity is a sum of these amplitudes with nonnegative powers of $`Y` and nonnegative constants. Since $`Y(x)` also has nonnegative coefficients, it follows that 

$$`G(x;\mathbf L)=V(x)^h R_{g,p,\mathbf L}(x),\qquad
 [x^j]R_{g,p,\mathbf L}(x)\ge0.`

 Convergence follows from 9.27. Hence 

$$`\left|\frac{G(x\mathrm e^{i\theta};\mathbf L)}{G(x;\mathbf L)}\right|
 \le\left|\frac{V(x\mathrm e^{i\theta})}{V(x)}\right|^h.`



Suppose first that $`k=n-p\to\infty`, and choose $`x` by $`h\Psi(x)=k`. Put $`\sigma^2=h\mathscr D\Psi(x)`. For fixed real $`u`, the ratio of the centered moment generating functions associated with $`G` and $`F` is 

$$`\frac{(G/F)(x\mathrm e^{u/\sigma};\mathbf L)}
 {(G/F)(x;\mathbf L)}.`

 It tends to one, uniformly in $`\mathbf L`. To see this, the endpoint expansions 9.3 and the quadratic inverse at $`x_c` show that 

$$`\sup_{0<x<x_c}\frac{xY'(x)}{\sqrt{\mathscr D\Psi(x)}}<\infty.`

 On the tilted interval $`x\mathrm e^{u/\sigma}` the model variance is comparable to its value at $`x`, and the interval remains subcritical. Therefore $`Y(x\mathrm e^{u/\sigma})-Y(x)=O_u(h^{-1/2})`. Now use 9.27 and the bounded derivative of $`\mathfrak b_Y`.

The real Gaussian limit 9.6 thus holds for $`G` with the same center $`k` and scale $`\sigma`. Its Fourier bound 9.28 is identical to the one used in 9.8–9.14. Fourier inversion consequently gives the local limit 9.7 for $`G` as well. At the common index $`k`, both local probabilities are asymptotic to $`(\sqrt{2\pi}\sigma)^{-1}`. Their ratio tends to one, and hence 

$$`\frac{[x^k]G(x;\mathbf L)}{[x^k]F(x)}
 =\prod_i\mathfrak b_{Y}(L_i)(1+o(1)),\qquad
 \lambda(Y)=\frac{2(n-p)}{2g-2+p}.`

 All errors are uniform on the fixed length box, including along sequences tending to either endpoint of the parameter interval.

For bounded $`k`, pass to a subsequence on which $`k` is fixed. Equation {bpref "eq:TL23"}[6.15] at $`Y=0`, with $`p+k` markings, gives the fixed-cusp boundary estimate 7.19. This yields the same conclusion since the saddle then tends to zero.

Finally, replacing $`2(n-p)/(2g-2+p)` by $`n/g` changes the corresponding $`Y` by $`o(1)` uniformly in $`n\ge p`. Indeed, along a subsequence on which $`n/g` tends to zero, a positive finite limit, or infinity, both parameters have the same limit in $`[0,y_0]`. Continuity of $`\mathfrak b_Y(L)`, uniformly on the length box, proves 9.24. At $`Y=0`, $`T=\Delta=\pi^2/4`; expanding $`I_0` and integrating gives the first formula in 9.25. At $`Y=y_0`, the integrand is constant, which gives the second.
:::


