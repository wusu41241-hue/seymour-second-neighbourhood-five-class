Five Maximal Incoming Classes Suffice: Exact Certificates and Structural
Constraints for Seymour's Second-Neighbourhood Conjecture
Guanze Yu
English research preprint, 7 October 2026

Contents
  paper/main.tex                 Main article (27 pages in the supplied build)
  supplement/main.tex            Technical supplement (119 pages)
  supplement/sections/           Complete retained supplementary proofs
  journal-preamble.tex           Shared black-and-white A4 layout
  references.bib                 Checked bibliography, including preprint versions
  verification/                  Exact certificate tables and independent replays
  review/                        Scope, coverage and internal-review records

Build
Use XeLaTeX and BibTeX from a current TeX distribution with Latin Modern fonts.
No custom LaTeX plugin is required. On Windows PowerShell:
  ./build.ps1

Equivalent commands, executed from the indicated directories:
  cd supplement
  xelatex -interaction=nonstopmode -halt-on-error main.tex
  bibtex main
  xelatex -interaction=nonstopmode -halt-on-error main.tex
  xelatex -interaction=nonstopmode -halt-on-error main.tex
  cd ../paper
  xelatex -interaction=nonstopmode -halt-on-error main.tex
  bibtex main
  xelatex -interaction=nonstopmode -halt-on-error main.tex
  xelatex -interaction=nonstopmode -halt-on-error main.tex

Build the supplement first: the article imports its theorem numbers.
The build script places both final PDFs in output/pdf. Keep the two PDFs
together under the supplied names so cross-document links can resolve.

Exact certificate replay
From the package root, with standard Node.js:
  node verification/verify_small_core_certificates.js
  node verification/verify_core_pattern_certificates_independent.js

Expected: PASS for 59,809 labelled cores of orders one through five and
462,404 nonempty inequalities (522,213 including the empty patterns).
No optimizer, solver, network service or third-party Node package is needed.
Additional original research checks are grouped under verification/research_checks.
Their results and hypothesis scopes are separate from the exhaustive core tables.
Large external solver archives are indexed in the coverage record rather than
bundled as certified proof objects.

Scope and submission status
The author is Guanze Yu, as specified by the author for this release.
No affiliation, ORCID, funding, journal acceptance or external peer review is
asserted. Additional declarations may be required by the target journal.
This package is prepared locally for public deposit; it does not itself
establish that an upload has been published or that a DOI has been registered.
The document is a complete account of the stated partial results; it does not
claim a proof or counterexample for the full conjecture. Internal independent
proof reconstruction and exact replay do not replace external peer review.
A complete novelty/priority assessment and human scholarly approval remain
necessary before submission. The paper discloses AI assistance in drafting
and exploratory implementation.

Release metadata and licensing
The .zenodo.json file describes the intended preprint with Guanze Yu as author.
The paper, supplement, editable text and certificate data use CC BY 4.0.
The original verification and build programs use the MIT license.
See LICENSE.txt and LICENSE-CODE.txt for scope and attribution.
The review records describe the earlier unsigned manuscript build and are
historical internal evidence; release-review.txt records the subsequent
title and authorship update. The GitHub repository is
https://github.com/wusu41241-hue/seymour-second-neighbourhood-five-class
Zenodo deposit status and DOI registration still require verification.

Editorial decisions
The main article carries the unbounded core certificate, cloning and closure
arguments. The supplement retains the longer residual exclusions and the
separately scoped n=2delta+3 tools. Earlier results subsumed by stronger
theorems are identified as such. Imported work and partial solver branches
are attributed and are not presented as original general theorems.

Layout
A4, Latin Modern text and Computer Modern-compatible mathematics, black on
white, no decorative boxes. All formulas and code remain editable source.
The native editor interface was unavailable in the authoring session; the
supplied PDFs were compiled with the installed XeLaTeX toolchain and checked
both structurally and visually.
