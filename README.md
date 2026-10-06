# Five Maximal Incoming Classes Suffice

## Exact Certificates and Structural Constraints for Seymour's Second-Neighbourhood Conjecture

**Guanze Yu — research preprint, 7 October 2026**

This repository contains the manuscript, technical supplement, editable LaTeX
sources, exact certificate tables, and independent verification programs.

The principal computer-assisted theorem states that every finite nonempty
oriented graph with at most five inclusion-maximal incoming-neighbourhood
equivalence classes has an entire maximal class of Seymour vertices. The total
number of vertices and the sizes of the classes are unrestricted.

**These results do not prove or refute the full conjecture.** The paper is a
preprint, not a peer-reviewed journal publication. AI-assisted research,
drafting and implementation are disclosed in the manuscript.

## Read the paper

- [Main manuscript (27 pages)](output/pdf/Seymour_Manuscript_2026-10-07.pdf)
- [Technical supplement (119 pages)](output/pdf/Seymour_Supplement_2026-10-07.pdf)
- [Editable main source](paper/main.tex)
- [Editable supplementary source](supplement/main.tex)
- [Bibliography](references.bib)

Keep both PDFs together under their supplied filenames so cross-document
references can resolve.

## Representative results

- An exact incoming-pattern certificate formulation, universally feasible if
  and only if Seymour's conjecture holds.
- Complete integer certificates for all 59,809 labelled oriented cores of
  orders one through five, implying the unrestricted-order five-class theorem.
- Simultaneous outgoing-row copying and structural restrictions on suitable
  extremal counterexamples.
- Protection-preserving completion and closure methods, with original-graph
  constraints at median feeds.
- The necessary residual bound `2M - n >= 7` (at least 8 at even order) in the
  explicitly stated arc-set-minimal counterexample setting; `M` counts missing
  unordered vertex pairs and `n` is the order. This is not asserted for arbitrary
  oriented graphs.

The manuscript and supplement distinguish unconditional statements, additional
minimality hypotheses, finite certificates, exploratory computations, and open
steps. No claim of worldwide priority or external referee approval is made.

## Verify the exact certificates

From the repository root, using standard Node.js:

```sh
node verification/verify_small_core_certificates.js
node verification/verify_core_pattern_certificates_independent.js
```

Expected result: `PASS` for 59,809 cores and 462,404 nonempty pattern inequalities
(522,213 checks including empty patterns). The independent verifier reconstructs
the graphs with Boolean matrices. Neither replay needs a solver, network access,
floating-point tolerance, or third-party Node package.

The SHA-256 checksum of `verification/incoming_core_certificates_n5.json` is:

```text
c9fe139b76a3866a7bf17e408d12f344823fa1a54fca306fd656139e601bfd5a
```

Additional checks under `verification/research_checks/` have their own scopes;
they are not all exhaustive proofs. Historical review and provenance records
under `review/` are internal research records, not external peer review.

## Build

Install or use an existing XeLaTeX/BibTeX distribution with Latin Modern fonts,
then run in PowerShell:

```powershell
./build.ps1
```

The script builds the supplement first, then the manuscript, and places the
PDFs in `output/pdf/`. See [README.txt](README.txt) for equivalent commands.

## Citation and archival status

Author: Guanze Yu. Title: *Five Maximal Incoming Classes Suffice: Exact
Certificates and Structural Constraints for Seymour's Second-Neighbourhood
Conjecture*. Year: 2026. Resource type: research preprint.

[Zenodo metadata](.zenodo.json) is provided for GitHub release archiving.
No Zenodo DOI has been verified at this repository's initial publication.
A GitHub repository by itself is not evidence of a successful Zenodo deposit.

## Licenses

- Paper, supplement, editable text and original non-code supporting material:
  [Creative Commons Attribution 4.0 International](LICENSE.txt).
- Original verification and build programs:
  [MIT](LICENSE-CODE.txt).

Cited third-party works retain their own rights. No author affiliation, ORCID,
funding source or journal acceptance is inferred.

## Historical provenance

Absolute local computer paths were replaced in the public copy by descriptive
`historical-research/` and `historical-workspace/` labels. Those labels document
earlier research locations; they are not runtime dependencies or promised
directories in this repository. The primary certificate references are portable.
