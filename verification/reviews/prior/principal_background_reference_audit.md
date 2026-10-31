# Principal results: background and primary-reference audit

AI reference and interpretation review by `/root/palomar_requirements`, 30 October 2026. This is a documentary audit, not a human review, a new Lean proof, or a new Comparator run. The manuscript reviewed has SHA256 `1d30574bf6a09012c0492449d6860884c993b191837c9c0d2a9bd17080a3d0bc`. The companion JSON pins the local material inspected.

Corrected after Stage36 acceptance: the earlier report's Section 4 described an intermediate density-witness helper, rather than the final principal M03 interface. That description is superseded below. The original report (`83e1c85d...`), JSON (`6f34a159...`) and audit script (`b7c90743...`) are preserved byte-for-byte in `audit/history/principal_background_before_stage36_scope_correction/`.

No substantive missing boundary hypothesis, incorrect Gaussian-position normalization, or invalid infinite-information subtraction was found in the principal applications. Three small clarifications are suggested below. The standard identifications discussed here must remain distinct from the propositions actually selected for kernel checking.

## 1. Variational Dirichlet eigenvalue and convex boundaries

The manuscript defines its eigenvalue by the infimum over `H_0^1(Int K)` at lines 100–111. Its formal counterpart is the genuine infimum of the squared gradient/value norm quotient over the closure of compactly supported smooth tests. `DirichletSobolev.lean` and `DirichletRayleigh.lean` implement this construction with actual global value/gradient pairs and zero extension. The formal statement therefore concerns the stated variational quantity, with no arbitrary spectral proxy.

A primary reference for its customary operator interpretation is van den Berg–Hempel–Voigt, *L1-estimates for eigenfunctions of the Dirichlet Laplacian*, J. Spectr. Theory **5** (2015), 829–857, DOI 10.4171/JST/115. The introduction and Section 1, pp. 830 and 833–834, define the Friedrichs Dirichlet Laplacian through its `H_0^1` form, take compact smooth tests as a form core, and explicitly require no boundary regularity. Finite volume yields discrete spectrum; connectedness gives a simple first eigenvalue. A convex body's interior is bounded, nonempty and connected. Thus imposing a `C^2` boundary on the paper would be unnecessary. [Publisher's complete article](https://ems.press/content/serial-article-files/33560).

The selected principal statement does not separately construct a named Friedrichs self-adjoint operator and prove its equality with this variational infimum. That operator identification is standard interpretive background. Likewise, strict positivity, classical interior regularity and simplicity are not conclusions supplied by the stopped DeGiorgi source port. The formal principal proof obtains a suitable actual weak log-concave ground state by a different proved construction; the independent proof-departure audit should describe that distinction.

## 2. Ground-state log-concavity

The manuscript's attribution to Brascamp–Lieb is appropriate. The original publication's title, authors, journal, year, volume, issue, pages and DOI match its bibliography. The original article's complete theorem text was not accessible through the publisher during this audit, so this review does not claim a direct reading of its Theorem 6.1. [Publisher record](https://www.sciencedirect.com/science/article/pii/0022123676900045).

An additional primary proof is Bryan–Clutterbuck–Rankin, *Convexity inequalities for eigenvalues and log-concavity of eigenfunctions*, arXiv:2605.01334v1. Its Theorem 1.3 explicitly states the first-eigenfunction log-concavity result on a convex domain with a convex potential and identifies it as Brascamp–Lieb, Theorem 6.1. Its proof discussion distinguishes a regular-domain argument from approximation on convex domains. This supports the citation's meaning; it does not justify silently adding a smooth-boundary hypothesis to the original theorem. [Complete primary text](https://arxiv.org/html/2605.01334v1).

Optional bibliographic precision: change the ground-state citation to `\cite[Theorem~6.1]{BL76}`. There is no need to expand the manuscript into a new regularity or strong maximum principle proof under the revised scope.

## 3. Gaussian position and the ellipsoid intersection consequence

Bobkov's actual statements match the use at manuscript lines 310–386. Proposition 3.1 characterizes a maximal Gaussian measure position by scalar covariance. Lemma 4.1 gives its absolute lower and upper bounds when the symmetric body has volume one. Bobkov's word “isotropic” here allows a scalar covariance; it does not assert the identity covariance used in the manuscript's later definition. The manuscript correctly retains the scalar `alpha`.

Theorem 1.1 and Corollary 2.3 together give a universal lower bound on the volume-one ellipsoid intersection functional. Ellipsoids are origin-centered by Bobkov's explicit convention. This validates the stated intersection consequence and the volume normalization before the determinant-one change of variables. It is an intersection consequence, not a claim that every covering formulation of an M-ellipsoid has been formalized. [Bobkov's complete author-hosted paper](https://www-users.cse.umn.edu/~bobko001/papers/2011_Contemp.%20Math.On.Milman%27s.ellipsoids.pdf).

The existing Milman attribution should remain. For a precise secondary locator within this primary research paper, `\cite[Theorem~1.1 and Corollary~2.3]{Bob11}` can accompany the intersection display. The current citation is already mathematically appropriate.

## 4. Log-concave laws and density representatives

The final accepted M03 interface is `InformationSpectrumLogConcaveMeasure.lean`, not the earlier density-witness helper `InformationSpectrumLaw.lean`. Its `information_spectrum_logConcaveMeasure_uniform_constant` takes the conventional compact-set condition `IsLogConcaveMeasure n nu`, evenness, isotropy, the prescribed Poincare bound and finite actual relative Fisher information. It does **not** take a density witness as an additional premise. The constant is chosen before dimension, law and supporting body.

The actual theorem `finite_relativeFisher_logConcaveMeasure_exists_density` first derives absolute continuity from finite relative information. In `LogConcaveMeasureDensity.lean`, normalized closed-ball masses are log-concave; Mathlib's Besicovitch differentiation theorem identifies their almost-everywhere limit with the Radon–Nikodym derivative. The chosen measurable pointwise log-concave liminf is everywhere finite by its positive finite mass. It represents the same law. M03 then applies the earlier density-form estimate. Thus there is no unformalized density-representative prerequisite for this finite-information principal theorem.

Stage36's saved certificate `audit/stage36_verification.json` has SHA256 `65932fa0e2b39e685e8c2ee0a28bf4337154e7f859edd9ca10951a6df61a59f5`. Its actual ordinary sandboxed Comparator log records all six kernel acceptances, the positive verdict and exit 0, in 1385.118 seconds. I inspected that existing log and these actual source headers/bodies; I did not launch another checker. This supersedes the earlier audit's limitation to a density formulation.

Borell's *Convex measures on locally convex spaces*, Ark. Mat. **12** (1974), 239–252, DOI 10.1007/BF02384761, Theorem 1.1, remains a suitable primary reference for the broader affine-support density characterization, including the log-concave case. Full arbitrary-law Borell equivalence, including potentially singular laws on a proper affine support, is not claimed as the selected formal theorem and is not needed to bridge M03. [Complete original scanned article](https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7214-11512_2006_Article_BF02384761.pdf).

An explanatory density-convention sentence may be useful for readers, but it must not suggest that the formal principal result assumes more than the manuscript's set-based log-concavity and finite-information domain.

## 5. Fisher information, entropy and time normalization

The square-root Sobolev definition of ordinary information in manuscript lines 239–249 agrees with `FisherInformation.lean`. The measure-level definitions use an actual Radon–Nikodym density, prove independence from its almost-everywhere representative, and take the value infinity outside the relevant absolute-continuity/Sobolev domains. Relative information additionally checks the second moment. They do not differentiate an arbitrary Radon–Nikodym representative pointwise.

The manuscript already introduces the relative-information formula under a finite-second-moment condition and justifies the cutoff identity by two `L^2` bounds. For clarity, its subsequent sentence can begin: “If the second moment and `J(nu)` are finite, ...”. This prevents the displayed identity from being read as unrestricted arithmetic involving infinity. The isotropic instances have the required moment, and their finite-information identities do not subtract infinities. This is a clarification, not a detected failure of a principal application.

Ledoux–Nourdin–Peccati's actual definitions and constants agree with the Gaussian normalization: their Theorem 2.2 is stated for a centered law with a smooth density relative to the standard Gaussian, and Proposition 2.4 contains integrated de Bruijn under the section's assumptions. Section 2.3 uses generator `Delta - x dot grad`, matching the manuscript's `exp(-t)` and `sqrt(1-exp(-2t))`. This is distinct from the Brownian generator `Delta/2` later used for the heat kernel. The cited smooth theorem alone should not be described as supplying the nonsmooth Sobolev extension; that extension needs its own proved approximation/endpoint argument, which the formal source develops. [Complete primary text, arXiv:1403.5855v2](https://arxiv.org/pdf/1403.5855).

Bakry–Gentil–Ledoux's bibliographic entry matches the publisher's 2014 volume 348 and DOI. Only publisher metadata and the accessible front matter/table of contents were available, not the entire book's proofs. This review therefore does not certify a direct reading of every cited book theorem. [Publisher record](https://link.springer.com/book/10.1007/978-3-319-00227-9).

## 6. Scope and stopped checks

This audit found no required change to the principal theorem's dimension, body class, determinant condition or universal-constant quantifier order. It supplies primary-source interpretation, not a claim that all manuscript intermediate displays have been checked. The separate principal statement audit and novel-argument audit retain their own independence boundaries; I authored parts of the reused formal source and do not label this a second independent mathematical review of those proofs.

The already completed background target `AffineFK.DeGiorgi.Crossover.LogGradient` compiled with exit 0 in 19.803 seconds, as preserved in `logs/branch_degiorgi/loggradient-build-10.txt`. All 26 source files and failed attempts are retained in `audit/degiorgi_loggradient_source_handoff.json` and its evidence archive. The planned fresh whole-26 named axiom batch was **never launched** after the scope change, and no own PDE Comparator was launched. No background check process remains running. The earlier frozen interface-12 evidence has 128 actual public-name axiom reports (126 original plus two explicitly checked Unicode names); it must not be represented as a fresh whole-26 report. No new proof or checker run was performed for this reference audit.
