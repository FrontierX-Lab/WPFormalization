import WPFormalization.Statements
import WPBlueprint.Chapters.C18
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "appD-extraction" =>

# Coefficient extraction with inverse-genus errors

This appendix proves Theorems {bpref "thm:sharp-extraction"}[10.1] and {bpref "thm:canonical-expansion"}[10.2]. Subsection D.1 makes the local limit theorem of Section 9 quantitative; its complex comparison and Fourier estimates are reused afterwards. Subsections D.2–D.4 prove Theorem {bpref "thm:sharp-extraction"}[10.1], and Subsections D.5–D.7 prove Theorem {bpref "thm:canonical-expansion"}[10.2] and compute its first coefficient.

## A quantitative local limit

We first make the local limit theorem 9.7 quantitative. The argument transfers a real-axis error to a complex neighborhood and applies Fourier inversion; the positive convolution factor controls the remaining part of the integral. This gives a power-rate bound. The complex comparison and Fourier estimates established in the proof will also be used in Subsection D.2, where retaining a Poisson factor gives an inverse-genus error uniformly over all coefficient indices.

:::proposition "prop:quantitative-local" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-Phi")
%%%
source := { document := "paper-v3", spans := #[{ page := "88", anchor := "prop:quantitative-local", citation := "Proposition D.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition D.1 — prop:quantitative-local.

Fix $`p\ge1`, and use $`h,\mu,\sigma` from {bpref "eq:TL37"}[9.4]. There are constants $`C_p,\kappa_p>0` such that, with $`M=\min(h,\mu)`, 

$$`\sup_{k\in\mathbb Z}
 \left|\sigma\mathbb P_x(N=k)-
 \frac{\mathrm{e}^{-(k-\mu)^2/(2\sigma^2)}}{\sqrt{2\pi}}\right|
 \le C_p M^{-\kappa_p},`

 whenever $`M` is sufficiently large, uniformly for $`0<x<x_c`.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "prop:quantitative-local" (uses := "lem:convolution, prop:marked-ratios, lem:parameter")
Write $`Z=(N-\mu)/\sigma` and $`\mathcal L(z)=\mathbb E_x \mathrm{e}^{zZ}`. The integral identity 9.5 and the convergent endpoint expansions 9.3 give constants $`c,C_p>0` for which 

$$`\left|\log\mathcal L(u)-\frac{u^2}{2}\right|
 \le C_p M^{-1/2}(|u|+|u|^3),\qquad |u|\le c\sqrt M.`

 To check the uniformity, note that near zero $`\Psi,\mathscr D\Psi` and $`\mathscr D^2\Psi` are comparable to $`x`, so the model Taylor remainder is $`O(|u|^3/\sqrt\mu)` and the integrated error is $`O(|u|x/\sqrt\mu)`. On an interior compact interval both are $`O_p(h^{-1/2}(|u|+|u|^3))`. Near criticality, $`\sigma\asymp\sqrt h/\varepsilon`; for $`|u|\le c\sqrt h` the tilted distance to the critical point stays comparable to $`\varepsilon`. The bounds $`\Psi=O(\varepsilon^{-1})` and $`\mathscr D^2\Psi=O(\varepsilon^{-3})` give the same estimate. Shrinking $`c` ensures the real moment generating function is defined on the whole interval. As before, the error in 6.20 is never differentiated.

Put $`T=\sqrt{\log M/80}` and $`f(z)=\mathcal L(z)-\mathrm{e}^{z^2/2}`. The function is analytic on $`|z|\le4T`. Positivity gives $`|\mathcal L(z)|\le\mathcal L(\Re z)`, whence D.2 implies 

$$`\sup_{|z|\le4T}|f(z)|\le2\mathrm{e}^{9T^2}=B,\qquad
 \sup_{u\in[-T,T]}|f(u)|
 \le C_p M^{-1/2}(1+T)^3\mathrm{e}^{T^2}=b.`

 For sufficiently large $`M`, $`b\le B`. In the disk $`|z|<4T` slit along $`[-T,T]`, the harmonic measure of the slit is at least $`1/2` for $`|z|\le T`. To check this, rescale $`T` to one and use $`G(w)=\log|w+\sqrt{w^2-1}|`, with the branch at infinity. It vanishes on the slit, is at most $`\log(1+\sqrt2)` on $`|w|\le1`, and is at least $`\log(4+\sqrt{15})` on $`|w|=4`. The maximum principle compares harmonic measure to $`1-G/\log(4+\sqrt{15})`, which is at least $`1/2` on the inner disk. Applying the two-constants principle to $`\log|f|` therefore yields 

$$`|f(it)|\le\sqrt{bB}
 \le C_p M^{-1/4}(1+T)^{3/2}\mathrm{e}^{5T^2},\qquad |t|\le T.`

 Its integral over this interval is $`O_p(M^{-1/8})`.

The Fourier estimates of Section 9.3 give constants $`c_0,c_1,C>0` such that 

$$`\int_{T<|t|\le\pi\sigma}|\mathbb E_x \mathrm{e}^{itZ}|\,\mathrm{d}t
 \le C\mathrm{e}^{-c_0T^2}+C\mathrm{e}^{-c_0h},\qquad 1\le T\le c_1\sqrt M.`

 Away from a fixed critical neighborhood this follows from 9.8: the product of the zero and one probabilities of $`V(xz)/V(x)`, divided by $`\mathscr D\Psi(x)`, is bounded below. Near zero both numerator and denominator are comparable to $`x`. In the critical neighborhood 9.11 becomes $`(1+c t^2/h)^{-h/8}`. For $`|t|\le\sqrt h` this is bounded by $`\mathrm{e}^{-c't^2}`. Beyond $`\sqrt h`, split the exponent in half, bound one half at $`\sqrt h`, and integrate the other against a fixed integrable power. The integral is $`O(\mathrm{e}^{-c'h})`. The outer arc is exponentially small uniformly in $`\varepsilon` by 9.14. These observations prove D.5.

Fourier inversion, D.4, D.5, and the Gaussian Fourier tail prove D.1. The three contributions are $`O_p(M^{-1/8})`, $`O(M^{-c_0/80})+O(\mathrm{e}^{-c_0h})`, and $`O(\mathrm{e}^{-T^2/2})=O(M^{-1/160})`, so one may take $`\kappa_p=\min(c_0,1/2)/80`. This exponent is not intended to be sharp.
:::



For the finite set of marking counts $`p=1,2,3`, choose a common exponent $`\kappa>0`. At the common saddle 9.15, put $`M=\min(2g-1,n-1)`. Repeating the coefficient comparisons in 9.16–9.21 now gives 

$$`B_{g,n}=\frac{\pi^2}{2r(Y)}(1+O(M^{-\kappa})),\qquad
 C_{g,n}=\frac{\pi^2(n-1)}{gx}(1+O(M^{-\kappa}))`

 when $`g,n\to\infty`. The center shift in 9.19 contributes only $`O(g^{-1})`, since its Gaussian argument is $`O(g^{-1/2})`.

The next three subsections prove Theorem {bpref "thm:sharp-extraction"}[10.1]. We first compare the true and the model generating functions on small complex neighborhoods of the real saddle point, and then treat large and small coefficient indices separately.

## Local complex comparison

To extract a coefficient by a contour integral we need the marked expansion on complex neighborhoods of the real saddle, not only on the real axis. We transfer a finite-order expansion to such neighborhoods and compare the true and model Fourier integrals.

Choose a fixed finite order $`K`, to be enlarged below, and define 

$$`F_{h,[K]}(z)=\frac{\mathcal J_{g,p}(z)}\pi
       \left(1+\sum_{j=1}^K\frac{\mathcal L_{p,j}(z)}{h^j}\right).`

 This is initially a local analytic function near the positive real interval. We do not assume that it is analytic on a whole cusp-weight disk. Theorem {bpref "thm:full-expansion"}[8.2] gives its real relative error $`O_{p,K}(h^{-K-1})`.

The convergent endpoint expansions and compactness give a fixed $`c>0` such that all functions in D.7 are analytic at $`z=x\exp(w/\sigma)` for $`|w|\le c\sqrt M`. Near zero this is an ordinary inverse-function neighborhood. Near criticality the radius in $`z` is proportional to $`x_c-x`, and $`\sigma(x_c-x)/x\asymp\sqrt h`; the square-root inverse and the analytic $`\delta` coefficients give the required branch. Each fixed collection of $`\mathcal L_{p,j}` is bounded on a smaller such neighborhood. The model derivatives obey 

$$`\frac{h\mathscr D^mS}{\sigma^m}=O_m(M^{1-m/2})\quad(m\ge3),
 \qquad
 \frac{\mathscr D^m\log B_p}{\sigma^m}=O_{p,m}(M^{-m/2})\quad(m\ge1).`

 At zero use $`\mathscr D^mS=2x+O_m(x^2)` and $`\mathscr D^m\log B_p=O_{p,m}(x)`. At criticality, with $`\varepsilon=1-x/x_c`, both numerator derivatives before their $`h` factor are $`O(\varepsilon^{-m})`, whereas $`\sigma\asymp\sqrt h/\varepsilon`. These bounds also hold locally in the complex neighborhoods by the same convergent expansions.

Put 

$$`\mathcal L_h(w)=\mathrm{e}^{-kw/\sigma}
   \frac{F_h(x\mathrm{e}^{w/\sigma})}{F_h(x)},\qquad
 \mathcal L_{h,[K]}(w)=\mathrm{e}^{-kw/\sigma}
   \frac{F_{h,[K]}(x\mathrm{e}^{w/\sigma})}{F_{h,[K]}(x)}.`

 Taylor expansion gives the disk bound $`C_{p,K}\mathrm{e}^{C|w|^2+C|w|}` for the centered, normalized true generating function and finite analytic model. For the true function, positivity bounds its modulus by its value at $`\Re w`, where the real expansion applies. No error term is differentiated. The explicit model also satisfies 

$$`\left|\frac{\mathcal J_{g,p}(x\mathrm{e}^{it/\sigma})}
                    {\mathcal J_{g,p}(x)}\right|
       \le C_p \mathrm{e}^{-c't^2},\qquad |t|\le c\sqrt M,`

 for sufficiently large $`M`. Indeed the real action has leading term $`-t^2/2`; its first omitted real term is $`O(t^4/M)`, and the real amplitude change is $`O_p(t^2/M)`. Shrinking $`c` absorbs the former, and growing $`M` absorbs the latter.

Take $`T^2=A_0\log h`, with $`A_0` large enough that the Fourier tail D.5 of the true distribution, the polynomial-Gaussian tails below, and the sparse-model Fourier tail below are $`O(h^{-3})`. These tail constants depend on the fixed action $`S` and amplitude $`B_p`, not on the finite truncation order. The central truncation order will first be fixed below; then choose $`C_0` so that $`M\ge C_0\log h` implies $`4T\le c\sqrt M` for its analytic neighborhood.

:::lemma_ "lem:local-comparison" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:CE1")
%%%
source := { document := "paper-v3", spans := #[{ page := "90", anchor := "lem:local-comparison", citation := "Lemma D.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma D.2 — Local comparison.

There are a fixed order $`K_c` and a constant $`C_0` such that, uniformly for $`M\ge C_0\log h`, 

$$`\sigma\mathbb P_x(N=k)=\frac1{2\pi}\int_{-T}^{T}\mathcal L_{h,[K_c]}(it)\,\mathrm dt
 +O(h^{-2}),\qquad T^2=A_0\log h.`


:::



:::proof "lem:local-comparison" (uses := "thm:full-expansion, prop:quantitative-local, ext:complex-analysis")
The difference between the two centered, normalized functions has real-slit bound $`C h^{-K-1}\mathrm{e}^{CT^2}` on $`[-T,T]` and disk bound $`C\mathrm{e}^{C'T^2}`. The harmonic-measure argument of D.4 then gives 

$$`\sup_{|t|\le T}|\mathcal L_h(it)-\mathcal L_{h,[K]}(it)|
       \le C_{p,K}h^{-(K+1)/2+C''A_0}.`

 The exponential constants here are independent of $`K`: for each fixed $`K`, the modulus of its finite correction factor lies between $`1/2` and $`2` on the chosen neighborhoods for all sufficiently large $`h`. Only the threshold and multiplicative constants depend on $`K`. Fix the central order $`K=K_c` sufficiently large that the integral of D.10 is $`O(h^{-2})`, and then fix $`C_0`. Thus $`\sigma\mathbb P_x(N=k)` equals the centered finite-model integral on $`[-T,T]`, divided by $`2\pi`, up to $`O(h^{-2})`. The normalization $`F_{h,[K]}(x)/F_h(x)=1+O(h^{-K-1})` is retained when recovering coefficients. All orders chosen here are fixed independently of $`g,x,k`.
:::



## Cancellation of the Poisson singularity

For indices with $`M\ge h^{1/4}` we compute the model coefficient by the saddle-point method. The coefficients of its Gaussian expansion have poles $`\Psi^{-j}` as the cusp weight tends to zero. These poles are exactly the terms of the expansion of $`\sqrt{2\pi k}\,\mathfrak p_k`, so they cancel after division by the Poisson factor in 10.2.

:::lemma_ "lem:large-indices" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:CG1")
%%%
source := { document := "paper-v3", spans := #[{ page := "90", anchor := "lem:large-indices", citation := "Lemma D.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma D.3 — Large indices.

The estimate 10.2 holds uniformly for integers $`k\ge h^{1/4}`.
:::



:::proof "lem:large-indices" (uses := "lem:local-comparison")
Here $`M=\min(h,k)\ge h^{1/4}`. Put $`b=\log B_p`. For a formal variable $`u` define the model polynomials through the exponential 

$$`\exp\!\left\{
 \sum_{m\ge3}u^{m-2}\frac{\mathscr D^{m-1}\Psi}{m!v^{m/2}}w^m
 +\sum_{m\ge1}u^m\frac{\mathscr D^mb}{m!v^{m/2}}w^m\right\}.`

 Let $`E_j(x)` be the Gaussian Fourier integral of its $`u^{2j}` coefficient: replace $`w^{2a}` by $`(-1)^a(2a-1)!!` and odd powers by zero. Each coefficient uses only finitely many derivatives. By Lemma {bpref "lem:local-comparison"}[D.2] it suffices to evaluate the central model integral. Expansion under the Gaussian bound D.9 gives 

$$`\frac1{2\pi}\int_{-T}^T \mathrm{e}^{-ikt/\sigma}
       \frac{\mathcal J_{g,p}(x\mathrm{e}^{it/\sigma})}{\mathcal J_{g,p}(x)}\,\mathrm{d}t
 =\frac1{\sqrt{2\pi}}\left(1+\sum_{j=1}^3\frac{E_j(x)}{h^j}
                                  +O_p(M^{-4}+h^{-2})\right).`

 To justify the stated remainder, retain weights through seven in D.11; a term of weight $`q` has parity $`q` in $`w`, so odd weights integrate to zero. The remaining terms are bounded by $`M^{-4}` times a fixed polynomial in $`|t|` times $`\mathrm{e}^{-c't^2}`. Their integral is $`O(M^{-4})`. The cutoff is $`O(\sqrt{\log h})`, which is smaller than any fixed positive power of $`M` in this range; the Taylor remainder and exponential remainder bounds therefore apply uniformly. The removed polynomial-Gaussian tails are $`O(h^{-2})` by the initial choice of $`A_0`. Replacing the finite model by $`\mathcal J` in its central integral costs $`O_p(h^{-1})`, by boundedness of its corrections and D.9.

The coefficients $`E_j` are bounded at criticality by D.8. Near zero, $`v=\Psi+O(\Psi^2)` and $`\mathscr D^m\Psi=\Psi+O_m(\Psi^2)`. In a monomial of weight $`2j` with $`a` action factors and $`b_*` amplitude factors, the total degree in $`w` is $`2j+2a`. Its leading power in $`\Psi` is therefore $`\Psi^{b_*-j}`. Every amplitude factor, or higher term in an action coefficient, improves the pole by at least one. Consequently 

$$`E_j(x)=s_j\Psi(x)^{-j}+O_{p,j}(\Psi(x)^{1-j})
       \quad(x\downarrow0),`

 where $`s_j` is the coefficient of $`k^{-j}` in $`\sqrt{2\pi k}\,\mathfrak p_k`. Indeed the leading action terms in D.11 are exactly those of a centered Poisson law. Parity makes the remaining Laurent powers integral. For example, direct Gaussian integration gives 

$$`E_1=-\frac{\mathscr D^2b+(\mathscr Db)^2}{2v}
      +\frac{(\mathscr Db)\mathscr D^2\Psi}{2v^2}
      +\frac{\mathscr D^3\Psi}{8v^2}
      -\frac{5(\mathscr D^2\Psi)^2}{24v^3}.`

 The amplitude terms are needed because $`k=h\Psi` is a model center, not an assertion about the exact finite-genus mean.

Divide D.12 by the central Poisson expansion $`\sqrt{2\pi k}\,\mathfrak p_k=1+\sum_{j=1}^3s_j/(h\Psi)^j+O(k^{-4})`. The principal pole cancels at each order. The quotient coefficients $`R_j` satisfy 

$$`|R_j(x)|\le C_{p,j}(1+\Psi(x)^{1-j}),\qquad j=1,2,3.`

 This follows inductively: a product of a Poisson pole of order $`i` and a previous quotient pole of order at most $`j-i-1` has order at most $`j-1`. The quotient is bounded at the critical end as well. Since $`k=h\Psi\ge1`, every $`h^{-j}R_j` is $`O_p(h^{-1})`. Also $`M^{-4}\le h^{-1}`. Combining this with D.10 and the bounded finite amplitude corrections proves 10.2 in this range.
:::



## Small coefficient indices

For $`k\le h^{1/4}` the saddle is too close to the origin for the Gaussian method. We expand the model coefficient directly around the Poisson coefficient of $`\mathrm e^{\mathfrak s_1hz}`.

:::lemma_ "lem:small-indices" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:CG1")
%%%
source := { document := "paper-v3", spans := #[{ page := "91", anchor := "lem:small-indices", citation := "Lemma D.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma D.4 — Small indices.

The estimate 10.2 holds uniformly for integers $`0\le k\le h^{1/4}`.
:::



:::proof "lem:small-indices" (uses := "lem:local-comparison, thm:full-expansion")
Near zero write $`S(z)=\mathfrak s_1z+\mathfrak s_2z^2+O(z^3)`, $`\mathfrak s_1=2`, and $`B_p(z)=1+d_1z+O(z^2)`. The full model D.7 is analytic on a fixed neighborhood of zero. For $`k\le h^{1/4}`, coefficient majorants give 

$$`\frac{k![z^k]F_{h,[K]}(z)}
      {(\mathcal J_{g,p}(0)/\pi)(\mathfrak s_1h)^k}
 =1+\frac{(\mathfrak s_2/\mathfrak s_1^2)k(k-1)+(d_1/\mathfrak s_1)k+\mathcal L_{p,1}(0)}h
       +O_{p,K}\!\left(\frac{(k+1)^4}{h^2}\right).`

 Factor $`\mathrm{e}^{\mathfrak s_1hz}` from the model. Its retained multiplier is $`1+h\mathfrak s_2z^2+d_1z+\mathcal L_{p,1}(0)/h`. Analytic absolute-coefficient majorants bound the omitted terms by convergent products starting with $`hz^3,h^2z^4,z^2,z/h,h^{-2}`. In convolution with the exponential, a degree-$`a` term contributes the factor $`(k)_a/(\mathfrak s_1h)^a`, bounded by $`(k/(\mathfrak s_1h))^a`. Evaluation of the majorants at that last argument gives the remainder in D.15; their exponent is $`O(k^2/h)=o(1)`. This avoids a spurious $`\sqrt k` loss from a supremum Cauchy estimate.

At the saddle, direct expansion gives the same polynomial without $`\mathcal L_{p,1}(0)` for the right-hand side of 10.2, relative to this Poisson baseline. Indeed, $`hS-k+k\log(k/(\mathfrak s_1hx))` contributes $`\mathfrak s_2k^2/(\mathfrak s_1^2h)`, $`\log B_p` contributes $`d_1k/(\mathfrak s_1h)`, and $`\tfrac12\log(k/(hv))` contributes $`-\mathfrak s_2k/(\mathfrak s_1^2h)`. Their error is $`O_p((k+1)^4/h^2)`. Thus model coefficient divided by the proposed saddle expression is $`1+O_p(h^{-1})` for $`k\le h^{1/4}`.

For $`C_0\log h\le k\le h^{1/4}`, comparison D.10 applies. Here the entire circle $`|z|=x` is inside the fixed zero-neighborhood. The convergent series for $`S` and $`|1-\cos(m\theta)|\le m^2(1-\cos\theta)` give 

$$`\Re(S(x\mathrm{e}^{i\theta})-S(x))\le-cx(1-\cos\theta),
 \qquad |\theta|\le\pi.`

 The model amplitude is bounded on this circle, and $`hx\asymp k`, so its standardized Fourier tail beyond $`T` is $`O(h^{-2})` by the initial choice of $`A_0`. Complete the central model integral to its full coefficient integral and apply D.15. This proves 10.2 in the middle sparse range. The scaled model central mass is bounded below by a positive constant here, by D.15 and the saddle comparison; therefore the additive central-integral errors remain relative errors.

For $`0\le k\le C_0\log h` use a different contour and, if needed, a different fixed truncation order $`K=K_\ell`, chosen after $`C_0`. Put $`\rho=(k+1)/(2h)` and consider $`(F_h(\rho z)-F_{h,[K]}(\rho z))/(\mathcal J_{g,p}(0)/\pi)` in the disk $`|z-1|<16` slit along $`[0,2]`. Both functions are analytic there for all large $`h`; only a fixed neighborhood of zero is used. Positivity, the real expansion, and the explicit model give disk bound $`C\mathrm{e}^{C'(k+1)}` and slit bound $`C_{p,K}h^{-K-1}\mathrm{e}^{C'(k+1)}`. On $`|z|=1` the slit harmonic measure is greater than $`1/2`: translate $`w=z-1`, so $`|w|\le2`, and compare the Green function in the proof of D.4 on radii two and sixteen. Its lower bound is 

$$`1-\frac{\log(2+\sqrt5)}{\log(16+\sqrt{255})}>\frac12.`

 Thus the unit-circle error is at most $`C_{p,K}h^{-(K+1)/2}\mathrm{e}^{C''(k+1)}=O(h^{-2})` upon fixing $`K` sufficiently large. Cauchy extraction changes the coefficient, relative to the baseline of D.15, by at most 

$$`Ch^{-2}\frac{k!}{(2h\rho)^k}
       =Ch^{-2}\frac{k!}{(k+1)^k}\le Ch^{-2}.`

 Equation D.15 and its saddle comparison finish this range, including $`k=0`. The two finite orders $`K_c,K_\ell` are fixed before $`h` tends to infinity, and each is used only in its own range. Enlarging the low-mean order does not change the already fixed central analytic neighborhood or $`C_0`.
:::



:::proof "thm:sharp-extraction" (uses := "lem:large-indices, lem:small-indices")
Lemmas {bpref "lem:large-indices"}[D.3] and {bpref "lem:small-indices"}[D.4] cover all $`k\ge0`; taking common constants proves the uniform assertion.
:::



## The analytic phase change at zero

To obtain an expansion that is uniform down to $`k=0`, we change variables so that the phase becomes exactly that of a Poisson coefficient, following Temme \[80\].

:::lemma_ "lem:phase-change" (parent := "paper_core") (tags := "paper-new") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "92", anchor := "lem:phase-change", citation := "Lemma D.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma D.5 — Analytic phase change.

Let $`S` be analytic near zero with $`S(0)=0` and $`S'(0)=s>0`, and let $`x=x(\nu)` be the solution of $`xS'(x)=\nu` near zero, so that $`x=\nu/s+O(\nu^2)`. There is a jointly analytic map $`z=Z(u,\nu)` on a fixed polydisk, with $`Z(0,\nu)=0`, such that 

$$`S(z)-\nu\log z=u-\nu\log u+\mathcal H(\nu),\qquad
 \mathcal H(\nu)=S(x)-\nu+\nu\log(\nu/x),\qquad Z(\nu,\nu)=x.`

 If $`H` is analytic near zero and $`f(u,\nu)=H(Z(u,\nu))\,uZ_u(u,\nu)/Z(u,\nu)`, then $`f` is jointly analytic, including at $`u=0`, and for all sufficiently small $`\nu=k/h`, 

$$`[z^k]\mathrm{e}^{hS(z)}H(z)
       =\mathrm{e}^{h\mathcal H(\nu)}[u^k]\mathrm{e}^{hu}f(u,\nu).`


:::



:::proof "lem:phase-change" (uses := "ext:complex-analysis")
The logarithmic equality in D.16 uses the nonvanishing coordinate quotient $`Z/u`. We construct $`Z` directly. Put $`c=\nu/x`, $`d=z-x` and $`\phi=S(z)-cz+\nu\log c-\mathcal H`. Then $`\phi(x,\nu)=\phi_z(x,\nu)=0`, and its double-zero quotient is $`\int_0^1(1-t)S''(x+td)\,\mathrm{d}t`, jointly analytic. Seek $`u=z(c+d\eta)`. The phase equation becomes 

$$`\frac{\phi}{d^2}-\eta+
 \nu\sum_{m\ge2}\frac{(-1)^{m-1}}m c^{-m}d^{m-2}\eta^m=0.`

 At $`z=\nu=0` it is $`S''(0)/2-\eta=0`, with derivative $`-1` in $`\eta`. The analytic implicit-function theorem gives $`\eta(z,\nu)`. Since $`u_z(0,0)=s`, the inverse $`Z` is jointly analytic on a fixed polydisk. The construction gives $`u(x,\nu)=\nu` and $`u(z,0)=S(z)`. Only local analyticity of $`S` is required.

The function $`f` is jointly analytic because $`Z/u` is analytic and nonvanishing. For D.17, write the coefficient as a residue and change variables $`z=Z(u,\nu)`; the circle $`|u|=\nu` lies in the fixed analytic neighborhood for all sufficiently small $`\nu`, and its image surrounds zero once.
:::



At the saddle, twice differentiating D.16 gives $`f(\nu,\nu)=H(x)\sqrt{\nu/v}`, with the positive branch. For $`H=B_p` the normalization on the right is exactly $`\mathrm{e}^{h\mathcal H}h^k B_p(x)\sqrt{\nu/v}/k!`, which equals the $`x`-dependent part of {bpref "eq:CG1"}[10.3].

## Poisson central polynomials with a uniform remainder

In the new variable the coefficient is a Poisson coefficient of an analytic amplitude. Expanding the amplitude about $`u=k/h` expresses it through the central polynomials $`T_m(k)` below; we bound the remainder uniformly in $`k`.

Define the normalized coefficient operator by 

$$`\mathscr P_{h,k}f=k!h^{-k}[u^k]\mathrm{e}^{hu}f(u,\nu),\qquad \nu=k/h.`

 Its central polynomial moments are 

$$`\mathscr P_{h,k}(u-\nu)^m=h^{-m}T_m(k),\qquad
 \sum_{m\ge0}T_m(k)\frac{t^m}{m!}=\mathrm{e}^{-kt}(1+t)^k.`

 Thus $`T_0=1`, $`T_1=0`; for $`m\ge2`, $`T_m` has degree at most $`\lfloor m/2\rfloor` and zero constant term. Write $`T_m(k)=\sum_{j=\lceil m/2\rceil}^{m-1}t_{m,j}k^{m-j}`.

:::lemma_ "lem:poisson-central" (parent := "paper_core") (tags := "paper-new") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "93", anchor := "lem:poisson-central", citation := "Lemma D.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma D.6 — Poisson central expansion.

Let $`f(u,\nu)` be jointly analytic and bounded by one on a fixed polydisk. There are $`\nu_0,C>0` such that, uniformly for $`0\le\nu=k/h\le\nu_0` and $`0\le K\le h/2`, 

$$`\begin{aligned}
 \mathscr P_{h,k}f&=\sum_{j=0}^Kh^{-j}\mathscr T_j[f](\nu)
       +O\!\left(C^{K+1}(K+1)!h^{-K-1}\right),\\
 \mathscr T_0[f]&=f(\nu,\nu),\qquad
 \mathscr T_j[f]=\sum_{m=j+1}^{2j}
 t_{m,j}\nu^{m-j}\frac{\partial_u^mf(\nu,\nu)}{m!}\quad(j\ge1).
 \end{aligned}`

 Moreover $`\|\mathscr T_j[f]\|\le C^{j+1}j!` on a smaller complex disk in $`\nu`, each $`\mathscr T_j[f]` with $`j\ge1` vanishes at $`\nu=0`, and $`|\mathscr P_{h,k}f|\le C`.
:::



:::proof "lem:poisson-central" (uses := "ext:complex-analysis, ext:stirling")
Choose $`\nu_0>0` small and a fixed Cauchy radius $`r` about every $`u=\nu`, with $`2\nu_0<r/2`. The Taylor remainder through degree $`2K+1` on $`|u|=\nu` is at most $`2r^{-2K-2}|u-\nu|^{2K+2}`. For $`k\ge1`, normalized coefficient extraction therefore bounds it by 

$$`\begin{aligned}
 &Cr^{-2K-2}\mathfrak p_k^{-1}\nu^{2K+2}
   \int_{-\pi}^{\pi}|\theta|^{2K+2}\mathrm{e}^{-ck\theta^2}\,\mathrm{d}\theta\\
 &\hspace{20pt}\le C^{K+1}(K+1)!\nu^{K+1}h^{-K-1}
       \le C_1^{K+1}(K+1)!h^{-K-1}.
 \end{aligned}`

 Here $`\mathfrak p_k^{-1}\le C\sqrt{k+1}` and $`1-\cos\theta\ge c\theta^2` on $`[-\pi,\pi]`. The Gaussian integral is an upper bound at every order, even when $`K` exceeds $`k`. At $`k=0` the operator is evaluation at zero and this remainder vanishes.

The retained moment terms above inverse order $`K` must also be bounded. The generating function in D.19 gives 

$$`|[k^a]T_m(k)|\le\frac{m!}{a!}
 [t^m]\left(\sum_{r\ge2}\frac{t^r}{r}\right)^a
 \le2^m\frac{m!}{a!},\qquad 1\le a\le m/2.`

 For $`\ell=m-a=K+1+d>K`, the retained range has $`0\le d\le K-1`, $`m\le2K+1`, and 

$$`\frac{m!}{(m-\ell)!}\le\frac{(2K+1)!}{(K-d)!}
       \le C^K(K+1)!K^d.`

 The sum of $`(K/h)^d` is bounded when $`K\le h/2`; the polynomial number of terms is absorbed into $`C^K`. At $`K=0` this sum is empty. This proves D.20. At order $`j`, $`m!/(m-j)!\le(2j)!/j!\le4^jj!`. Cauchy’s bound thus gives $`\|\mathscr T_j[f]\|\le C^{j+1}j!` on one smaller complex $`\nu` disk. Each positive-order coefficient vanishes at zero. The same contour estimate with no vanishing factor gives $`|\mathscr P_{h,k}f|\le C\|f\|`.
:::



Apply Lemmas {bpref "lem:phase-change"}[D.5] and {bpref "lem:poisson-central"}[D.6] to $`f_s(u,\nu)=B_p(Z(u,\nu))\mathcal L_{p,s}(Z(u,\nu))uZ_u/Z`. Put $`f_0^*(\nu)=B_p(x)\sqrt{\nu/v}`, which is bounded away from zero on a fixed small complex disk, with $`f_0^*(0)=1`. The extracted coefficients there are 

$$`\mathcal A_{p,j}(Y)=\frac1{f_0^*(\nu)}
       \sum_{s=0}^j\mathscr T_{j-s}[f_s](\nu),\qquad \nu=\Psi(X(Y)).`

 This proves their zero-end analyticity and endpoint values. The common norms of Theorem {bpref "thm:full-expansion"}[8.2] give $`\|f_s\|\le C_p\mathfrak B_p^s(s!)^2` on one polydisk. Applying D.20 at order $`K-s` uses $`(s!)^2(K-s+1)!\le((K+1)!)^2`. For a finite marked model of order $`J=\lfloor\kappa\sqrt h\rfloor>K`, the bounded operator controls all unused amplitudes by their first geometric tail term, since $`\mathfrak B_p(s+1)^2/h<1/2` through $`J`. Thus both model errors and coefficient norms have the required Gevrey bound. The functions D.22 agree with {bpref "eq:CG3"}[10.5] where both are defined; this is proved at the end of the proof of Theorem {bpref "thm:canonical-expansion"}[10.2], from the two expansions on a common range of densities.

## Proof of the uniform coefficient expansion

:::proof "thm:canonical-expansion" (uses := "thm:full-expansion, lem:phase-change, lem:poisson-central, prop:quantitative-local, ext:stirling")
We first replace the true generating function by one finite marked expansion, with exponentially small error after coefficient extraction. For small cusp density the Poisson calculation above applies. For the remaining densities we use uniform Gaussian coordinates and divide by the exact Poisson normalization. The last step absorbs the exponential comparison error into the stated remainder at every allowed order.

Write $`F_h=\Phi_g^{(p)}` and $`J_h=\mathcal J_{g,p}/\pi`. Choose a sufficiently small fixed $`\kappa>0`, set $`J=\lfloor\kappa\sqrt h\rfloor`, and use the single finite model 

$$`M_h(z)=J_h(z)P_J(z),\qquad
 P_J=\sum_{s=0}^J\mathcal L_{p,s}h^{-s}.`

 Theorem {bpref "thm:full-expansion"}[8.2] gives $`|F_h/M_h-1|\le C\mathrm{e}^{-a_0\sqrt h}` on the entire real interval. Its common coefficient norm also gives $`\|P_J-1\|\le C/h` on one complex parameter neighborhood, since the consecutive majorant ratio is $`\mathfrak B_p(s+1)^2/h<1/2`. All choices below use this same model. The constants in the two coefficient ranges can be chosen in the order $`d`, then $`\eta`, then $`\tau`; the small-disk argument below specifies the first two choices.

We first compare the true coefficients with those of this model. Put $`m_* =\min(h,k)` and, for $`k\ge1`, 

$$`\mathscr F_x(w)=\mathrm{e}^{-kw/\sigma}
       \frac{F_h(x\mathrm{e}^{w/\sigma})}{F_h(x)},\qquad
 \mathscr M_x(w)=\mathrm{e}^{-kw/\sigma}
       \frac{M_h(x\mathrm{e}^{w/\sigma})}{M_h(x)}.`

 There is a fixed $`c>0` on whose disks $`|w|\le c\sqrt{m_*}` the complex inverse parameter is defined and stays in the common coefficient neighborhood. At criticality, $`\varepsilon(x\mathrm{e}^{w/\sigma})/\varepsilon(x)=1+O(w/\sqrt h)`; choosing $`c` small fixes its square-root branch and keeps the tilted real radius below $`x_c`. Near zero use ordinary analytic inversion, and use compactness between the endpoints. The centered model action has zero first derivative and bounded second derivative: its second derivative is $`v(x\mathrm{e}^{w/\sigma})/v(x)`. The convergent endpoint expansions bound this ratio and the normalized logarithmic amplitude derivative. Consequently 

$$`|\mathscr M_x(w)|\le C\mathrm{e}^{C|w|^2+C|w|}.`

 Positivity bounds $`|\mathscr F_x(w)|` by $`\mathscr F_x(\Re w)`. On the real diameter the exact identity 

$$`\mathscr F_x(u)=\mathscr M_x(u)
 \frac{1+e_h(x\mathrm{e}^{u/\sigma})}{1+e_h(x)},\qquad
 e_h=F_h/M_h-1,`

 therefore gives the same disk bound and an additional factor $`\mathrm{e}^{-a_0\sqrt h}` for their difference on that diameter.

For a fixed small $`\eta>0`, take $`k\ge\eta\sqrt h` and $`T=\tau h^{1/4}`. Choose $`\tau>0` after $`\eta,a_0`, so that $`4T\le c\sqrt{m_*}`, $`T\le c_1\sqrt{m_*}` in D.5, and $`T<\pi\sigma`. The scale-invariant harmonic measure used in D.4 gives 

$$`\sup_{|t|\le T}|\mathscr F_x(it)-\mathscr M_x(it)|
 \le C\exp\{-a_0\sqrt h/2+C T^2+C T\}
 \le C\mathrm{e}^{-a_1\sqrt h}.`

 Its integral has the same bound after decreasing $`a_1`. The integrated tail D.5 of the true distribution is also exponentially small in $`\sqrt h`; the outer-arc estimate introduces no factor $`\sigma`. The model central integral is bounded by D.9 and the bounded $`P_J` ratio. Restoring the real normalization thus shows 

$$`\left|[z^k]F_h-
 \frac{x^{-k}}{2\pi\sigma}\int_{-T}^T
             \mathrm{e}^{-ikt/\sigma}M_h(x\mathrm{e}^{it/\sigma})\,\mathrm{d}t\right|
 \le C\mathcal Q_{g,p,k}\mathrm{e}^{-a_2\sqrt h}.`

 Indeed the error before division is at most $`CF_h(x)x^{-k}\sigma^{-1}\mathrm{e}^{-a_2\sqrt h}`, and $`\mathfrak p_k\sqrt k` is bounded above and below for integer $`k\ge1`. The real matching factor $`F_h(x)/M_h(x)=1+O(\mathrm e^{-a_2\sqrt h})` has been absorbed into the error.

For the remaining $`k`, put $`r=d/\sqrt h`. On $`|z|\le4r`, positivity and the near-zero model give $`|(F_h-M_h)/J_h(0)|\le C\mathrm{e}^{Chr}`; on $`[0,r]` this improves to $`C\mathrm{e}^{-a_0\sqrt h+Chr}`. In the disk $`|z-r/2|<2r` slit along $`[0,r]`, the slit harmonic measure is greater than $`1/4` on $`|z|\le r/4`. To see this, rescale to $`|w|<4` with slit $`[-1,1]`. On the target $`|w|\le3/2` its Green function is less than $`\log4`, and on $`|w|=4` it is greater than $`\log7`; comparison gives $`1-\log4/\log7>1/4`. Choose $`d` small, then $`\eta` small, so the two-constants bound is $`C\mathrm{e}^{-a_3\sqrt h}` and the saddle for $`1\le k<\eta\sqrt h` lies in $`|z|\le r/4`. Cauchy’s bound on $`|z|=x` is on the $`\mathcal Q` scale with a cost at most $`C\sqrt{k+1}`: $`v/\Psi` is bounded and $`J_h(x)/J_h(0)\ge c` near zero. This polynomial cost is absorbed into a smaller exponential. At $`k=0` use the marked estimate at zero directly.

Choose a switching density $`\nu_*>0` strictly inside the fixed Poisson neighborhood. For $`\Psi(x)\le\nu_*`, the full model circle is analytic and 

$$`\Re(S(x\mathrm{e}^{i\theta})-S(x))\le-cx(1-\cos\theta).`

 This follows from $`S(z)=2z+\sum_{m\ge2}\mathfrak s_mz^m` and $`\sum_{m\ge2}m^2|\mathfrak s_m|x^m=O(x^2)`, using $`1-\cos(m\theta)\le m^2(1-\cos\theta)`. The amplitudes are bounded, and $`hv\asymp k`, so the standardized model tail is Gaussian on the whole circle. For $`k\ge\eta\sqrt h` it completes the integral in D.23 to $`[z^k]M_h` at exponential precision. Together with the small disk, this compares the true coefficients with those of the full model for every $`\Psi(x)\le\nu_*`. The preceding Poisson argument now gives 10.6, with one additional fixed error $`C\mathrm{e}^{-a\sqrt h}`, throughout this range.

Uniform coordinates near criticality. For the other range we justify the growing-order Gaussian expansion uniformly through the critical point. In $`\delta=y_0-Y`, write the convergent local factors as 

$$`x_c-X(Y)=\delta^2\alpha(\delta),\quad
 \mathcal Z(Y)=\delta^{5/2}\zeta(\delta),\quad
 B_p(X(Y))=\delta^{p/2}\mathfrak b_p(\delta),\quad
 v(X(Y))=\delta^{-4}v_0(\delta),`

 where all four factors are analytic and nonzero at zero. For $`z=X(Y)\mathrm{e}^{iu/\sqrt v}` the inverse has $`\delta_z=\delta q(\delta,u)`, jointly analytic and close to one: divide its equation $`x_c-X(y_0-\delta q)=x_c-z` by $`\delta^2` and apply the implicit-function theorem at $`q=1,u=\delta=0`. Its $`q` derivative is $`2\alpha(0)\ne0`. Thus $`S(z)-S(x)` and $`B_p(z)/B_p(x)` are analytic joint families, expressed through $`\log q`, $`\zeta(\delta q)/\zeta(\delta)` and $`q^{p/2}\mathfrak b_p(\delta q)/\mathfrak b_p(\delta)`. Also $`\Psi/\sqrt v` extends analytically. Compactness gives common neighborhoods for $`\Psi\ge\nu_*/2`.

Set 

$$`\psi_Y(u)=S(x\mathrm{e}^{iu/\sqrt v})-S(x)-i\Psi u/\sqrt v,
 \qquad W_Y(u)=u\sqrt{-2\psi_Y(u)/u^2}.`

 The removable quotient is one at zero; $`W'_Y(0)=1`. On one fixed disk $`W_Y` has a jointly analytic inverse $`U_Y`, with $`\psi_Y(U_Y(w))=-w^2/2`. Put $`u_0=T/\sqrt h=\tau h^{-1/4}`. The image endpoints are $`\pm u_0+O(u_0^2)`. Straight connectors to $`\pm u_0` have length $`O(u_0^2)` and $`\Re(w^2)\ge u_0^2/2`. A finite contour deformation therefore costs at most $`C\sqrt h\,u_0^2\mathrm{e}^{-hu_0^2/4}`. After factoring $`J_h(x)x^{-k}/\sigma`, the central integral becomes 

$$`\frac{\sqrt h}{2\pi}\int_{-u_0}^{u_0}\mathrm{e}^{-hw^2/2}
       \sum_{s=0}^J\widetilde f_s(w,Y)h^{-s}\,\mathrm{d}w
       +O(\mathrm{e}^{-a\sqrt h}),`

 where $`\widetilde f_s=[B_p(z(U_Y(w)))/B_p(x)]
 \mathcal L_{p,s}(z(U_Y(w)))U'_Y(w)` has common norm $`C_p\mathfrak B_p^s(s!)^2` and $`\widetilde f_0(0,Y)=1`.

Gaussian expansion. For $`s\le K`, Taylor expand through degree $`2(K-s)+1` on that fixed disk. The absolute Gaussian moment bounds the remainder by $`C^{K-s+1}(K-s+1)!h^{-K+s-1}\|\widetilde f_s\|`. Odd terms vanish. To extend the polynomial moments to the whole line, use, for $`|w|\ge u_0`, 

$$`\mathrm{e}^{-hw^2/2}\le \mathrm{e}^{-hu_0^2/4}\mathrm{e}^{-hw^2/4}.`

 The remaining moment majorants $`C^j j!h^{-j}` have bounded sum for $`j\le K\le J=O(\sqrt h)`. All polynomial tails are therefore $`O(\mathrm{e}^{-a\sqrt h})`, even at growing Taylor degree. The unused $`s>K` amplitudes again form a geometric tail. The factorial convolution used above yields a numerator remainder $`CB^{K+1}((K+1)!)^2h^{-K-1}+C\mathrm{e}^{-a\sqrt h}`. After factoring $`1/\sqrt{2\pi}`, its coefficients have the same common-domain bounds and agree with 10.4. Indeed, for fixed $`Y` the model integral is defined for every real $`h`, and both families are the coefficients of its asymptotic expansion as $`h\to\infty` through real values: 10.4 before and the present ones after the analytic change of variable $`u=U_Y(w)`. Such expansion coefficients are unique.

The exact Poisson normalization. The divisor in {bpref "eq:CG1"}[10.3] is exact. Put $`R(k)=\sqrt{2\pi k}\,\mathfrak p_k`. Its logarithm satisfies 

$$`\log R(k)=-\int_0^\infty \mathrm{e}^{-kt}
 \left(\frac1{\mathrm{e}^t-1}-\frac1t+\frac12\right)\frac{\mathrm{d}t}{t}.`

 The kernel has a removable origin, analytic radius $`2\pi`, and is bounded on the positive axis. Its Taylor remainder through degree $`L-2` is bounded globally there by $`CD^Lt^{L-1}`: use Cauchy near zero and bound each retained power outside a fixed small interval. Integration gives $`CD^L(L-1)!k^{-L}`. For exponentiation and inversion, the degree-$`K` log polynomial is bounded on $`|t|\le1/(D_0(K+1))`. Cauchy’s tail at $`t=1/k`, for $`K\le c k`, is at most $`C[D_0(K+1)/k]^{K+1}\le C(\mathrm{e}D_0)^{K+1}(K+1)!k^{-K-1}`. Since the exponential is bounded on the relevant real interval, the remainder for $`\log R` transfers to $`R` and to $`R^{-1}`, which therefore have Gevrey-1 remainders. Here $`k\ge(\nu_*/2)h` and $`\Psi^{-1}` is bounded analytic through criticality. By {bpref "eq:CG1"}[10.3], $`\mathcal Q_{g,p,k}/(\mathcal J_{g,p}(x)x^{-k}/(\pi\sigma))
=R(k)/\sqrt{2\pi}`. The two factors $`1/\sqrt{2\pi}` cancel. Dividing the normalized numerator by $`R(k)` consequently preserves the Gevrey-2 error and gives exactly {bpref "eq:CG3"}[10.5].

Identification on the overlap. For $`\nu_*/2\le\Psi\le\nu_*` both expansions hold; write $`\mathcal A^{\mathrm P}_{p,j}` for the Poisson coefficients D.22 and $`\mathcal A^{\mathrm G}_{p,j}` for the Gaussian coefficients {bpref "eq:CG3"}[10.5]. Fixed-$`Y` uniqueness is not available directly, since $`k=h\Psi(X(Y))` must be an integer, so we argue by density. Suppose the two families agree below order $`j`. Subtracting the expansions at order $`K=j` gives $`\mathcal A^{\mathrm P}_{p,j}(Y_{h,k})-\mathcal A^{\mathrm G}_{p,j}(Y_{h,k})=O(h^{-1})`, uniformly over all admissible $`(h,k)` with $`Y_{h,k}` in the overlap, where $`h\Psi(X(Y_{h,k}))=k`. Given $`Y` in the open overlap, take $`k=\lfloor h\Psi(X(Y))\rfloor`; since $`\Psi\circ X` is continuous and strictly increasing, $`Y_{h,k}\to Y` as $`h\to\infty`. Both coefficients are continuous, so they agree at $`Y`. By induction the two families coincide on the open overlap. Both are analytic on $`0<\Psi(X(Y))<\nu_*`, so the identity theorem extends the equality to this whole interval. Hence D.22 is the analytic continuation of {bpref "eq:CG3"}[10.5] to $`Y=0`, and the coefficients are analytic on one complex neighborhood of $`[0,y_0]`.

Absorbing the residual error. It remains to absorb the fixed exponential error at every allowed order. After fixing the model, neighborhoods and cutoff, choose $`c_p<\kappa/2` so small that $`2c_p<1` and $`4c_p\log(\mathrm{e}/(2c_p))<a`. For $`L=K+1\le2c_p\sqrt h` and $`\mathfrak B_p\ge1`, 

$$`\mathfrak B_p^L(L!)^2h^{-L}
 \ge \mathrm{e}^{-2L\log(\mathrm{e}\sqrt h/L)}
 \ge \mathrm{e}^{-4c_p\log(\mathrm{e}/(2c_p))\sqrt h}.`

 This bounds the fixed residual by the stated remainder simultaneously for every $`K\le c_p\sqrt h`, including zero. Finally choose $`c'_p<c_p` after the final $`\mathfrak B_p`, with $`\mathfrak B_p(c'_p)^2<1`. The upper bound $`\mathfrak B_p^L(L!)^2h^{-L}\le(\mathfrak B_pL^2/h)^L` proves the exponential approximation at $`K=\lfloor c'_p\sqrt h\rfloor`.
:::



The first coefficient after extraction is

:::proposition "eq:CG12" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:CG3")
%%%
source := { document := "paper-v3", spans := #[{ page := "97", anchor := "eq:CG12", citation := "Equation D.24", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition D.24 — Explicit first extracted correction.

In the setup and notation of this section, the paper defines or asserts:



$$`\begin{aligned}
 \mathcal A_{p,1}={}&\mathcal L_{p,1}
 -\frac{\mathscr D^2b+(\mathscr Db)^2}{2v}
 +\frac{(\mathscr Db)\mathscr D^2\Psi}{2v^2}
 +\frac{\mathscr D^3\Psi}{8v^2}
 -\frac{5(\mathscr D^2\Psi)^2}{24v^3}+\frac1{12\Psi},
 \qquad b=\log B_p.
 \end{aligned}`


:::



Its apparent pole at zero is removable by D.22. In particular, retaining this term improves the relative remainder to $`O_p(h^{-2})` over every coefficient index.

At the critical endpoint its value is

:::proposition "eq:CG13" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:CG3")
%%%
source := { document := "paper-v3", spans := #[{ page := "48", anchor := "eq:CG13", citation := "Equation D.25", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition D.25 — Critical value of first correction.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal A_{p,1}(y_0)=-\frac{p^2}{8}+\frac p2-\frac{37}{60}.`


:::



Indeed, writing $`\varepsilon=1-x/x_c`, the leading terms are $`S=-(5/4)\log\varepsilon+O(1)` and $`\log B_p=(p/4)\log\varepsilon+O(1)`. Their differentiated convergent expansions give $`E_1(y_0)=-(p^2+4p)/40-1/15` in {bpref "eq:CG12"}[D.24]. Combine this with $`\mathcal L_{p,1}(y_0)=t_p` from {bpref "eq:ST13"}[8.1] and $`\Psi^{-1}\to0`.
