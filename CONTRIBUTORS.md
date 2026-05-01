# Contributors index

Canonical handle → identity mapping for everyone referenced in this project.

**Convention.** A handle is uppercase first-initial + surname (`PHAJEK` =
Pavel Hajek). Exception: `SWOLF` for Stephen Wolfram (historical). Project
docs and Lean comments refer to people by handle; the canonical full
identity lives here.

**Evidence policy.** This file states verifiable facts only, with citation
and the date the source was checked. Project-internal claims (e.g. "X
proposed Y in a meeting") are recorded in the relevant project doc, not
here. Where this file is silent on a person's affiliation or role, the
correct interpretation is "I have not verified this", not "they have no
affiliation".

Last verified against external sources: **2026-05-01**.

---

## Handles

| Handle | Full name | Wolfram Institute /people listing (verified 2026-05-01) |
|---|---|---|
| `SWOLF` | Stephen Wolfram | HEAD |
| `RASSAR` | Richard Assar | FELLOW |
| `PHAJEK` | Pavel Hajek | FELLOW |
| `NMURZIN` | Nikolay Murzin | FELLOW |
| `CZAPATA` | Carlos Zapata-Carratalá | FELLOW |
| `JWILES` | James Wiles | STRATEGIC INITIATIVES LEAD |
| `DHAMMOCK` | Dugan Hammock | TECHNICAL RESEARCH COORDINATOR |
| `UBAJAJ` | Utkarsh Bajaj | Affiliated Researcher |
| `JGORARD` | Jonathan Gorard | Alumnus |
| `PPOKORNY` | Pavel Pokorny | not listed |
| `HVLE` | Hông Vân Lê | not listed |
| `IMILEA` | Ioana Milea | not listed |
| `SAHMED` | Sara Ahmed | not listed |
| `HKOLCZ` | Hubert Kolcz | not listed |
| `JPULLMAN` | Jan Pullman | not listed |
| `SRODKEY` | Sam Rodkey | not listed |

Source for the /people column: <https://wolframinstitute.org/people> retrieved 2026-05-01.

"not listed" means the person is not on the Wolfram Institute /people page as of 2026-05-01. It does not imply they are not affiliated, only that I have not independently verified affiliation.

---

## Per-handle records

Each entry lists what is verifiable from external evidence. Project-internal references (M-task ownership, meeting-recorded ideas, etc.) live in their own files (INFRAGEOMETRY.md, NEXT_STEPS.md, INDEX.md, task tracker) and use the handle for cross-reference.

### `SWOLF` — Stephen Wolfram

- Wolfram Institute HEAD per <https://wolframinstitute.org/people> (2026-05-01).
- Founder/CEO of Wolfram Research.

### `RASSAR` — Richard Assar

- Wolfram Institute FELLOW per <https://wolframinstitute.org/people> (2026-05-01).
- Owner of this project (`infra_formalization`).
- Owner of `HypergraphRewritingEngine` (`efficient_rewriting_final/`) — the rule-search/multiway evolution engine the Lean executor cross-checks against.

### `PHAJEK` — Pavel Hajek

- Wolfram Institute FELLOW per <https://wolframinstitute.org/people> (2026-05-01).
- GitHub: <https://github.com/p135246>.
- LinkedIn: `dr-pavel-hajek`.
- Per /people page: PhD and postdoctoral work bridged Chern–Simons theory, string topology, symplectic geometry.
- Paclet authorship (per upstream `PacletInfo.wl` `Creator` field):
  - `InfraAnalysis` — Creator.
  - `SyntheticInfrageometry` — Creator.
  - `InfraCausality` — Creator.
- Paclet authorship (per git log, sole or majority committer):
  - `InfraAnalysis` — sole committer in upstream submodule history.
  - `SyntheticInfrageometry` — sole committer.
  - `InfraCausality` — sole committer.
  - `InfraGaugeTheory` — sole committer (note discrepancy with PacletInfo `Creator` field; see `PPOKORNY` below).
  - `Infrageometry` — one commit, "Adds simplicial sets" (2025-10-16, `SimplicialSet.wl`).

### `NMURZIN` — Nikolay Murzin

- Wolfram Institute FELLOW per <https://wolframinstitute.org/people> (2026-05-01).
- Per /people page: quantum computation, machine learning, Wolfram Language development.
- Paclet authorship:
  - `Infrageometry` — Creator (upstream `PacletInfo.wl`); principal substantive committer per git log (commits 2025-10-02 onward: hypergraph functionality, TDA, popular networks, complex hypergraph functionality, geodesics, Quantum Calculus module, testing framework, etc.).

### `CZAPATA` — Carlos Zapata-Carratalá

- Wolfram Institute FELLOW per <https://wolframinstitute.org/people> (2026-05-01).
- Per /people page: PhD in mathematical physics; leads the Arity Science Project; founded the Society for Multidisciplinary and Fundamental Research; developed the EntropyTCG strategy game.
- Surname is hyphenated: "Zapata-Carratalá" (per /people page). The shortened form "Carlos Zapata" used in legacy project docs refers to this person.

### `JWILES` — James Wiles

- Wolfram Institute STRATEGIC INITIATIVES LEAD per <https://wolframinstitute.org/people> (2026-05-01).
- GitHub: <https://github.com/Zaffer> (commits to the `Infrageometry` paclet appear under this account, email format `51871197+Zaffer@users.noreply.github.com`).
- Personal site: <https://jameswiles.com/>.
- Paclet contributions (per git log):
  - `Infrageometry` — initial repository commits (2024-04-19): initial commit, README + image, drawing; plus "Notebook additions" (2024-06-28). Repository was dormant from June 2024 until `NMURZIN` began substantive contributions in October 2025.

### `DHAMMOCK` — Dugan Hammock

- Wolfram Institute TECHNICAL RESEARCH COORDINATOR per <https://wolframinstitute.org/people> (2026-05-01).
- Per /people page: computational geometry specialising in hypershapes, aperiodic tilings, quasicrystals; geometric visualisation, art creation, research, mentoring.

### `UBAJAJ` — Utkarsh Bajaj

- Wolfram Institute Affiliated Researcher per <https://wolframinstitute.org/people> (2026-05-01).
- No further public detail verified.

### `JGORARD` — Jonathan Gorard

- Wolfram Institute Alumnus per <https://wolframinstitute.org/people> (2026-05-01).
- Subject of the audit arm of this project (papers arXiv:2004.14810, arXiv:2102.09363, arXiv:2303.07282, arXiv:2011.12174, arXiv:2308.07508, arXiv:2401.14209).

### `PPOKORNY` — Pavel Pokorny

- **Not listed** on the Wolfram Institute /people page as of 2026-05-01.
- Cited in upstream `resources/InfraGaugeTheory/InfraGaugeTheory/PacletInfo.wl` as `Creator -> "Pavel Pokorny"`. The `git log` of the same submodule shows no commits under the name "Pavel Pokorny"; all commits are by Pavel Hajek (see `PHAJEK`).
- Discrepancy noted; not resolved by external sources I have access to.

### `HVLE` — Hông Vân Lê

- Not listed on Wolfram Institute /people page as of 2026-05-01.
- A Hông Vân Lê is a published mathematician at the Czech Academy of Sciences with research in differential geometry, information geometry, and mathematics of machine learning; co-author of *Information Geometry* (Ay, Jost, Lê, Schwachhöfer; Springer 2017). Source: <https://ncatlab.org/nlab/show/H%C3%B4ng+V%C3%A2n+L%C3%AA>.
- Whether the project's "Van Le" references this Hông Vân Lê is not independently verified.

### `IMILEA` — Ioana Milea

- Not listed on Wolfram Institute /people page as of 2026-05-01.
- A LinkedIn profile <https://www.linkedin.com/in/ioana-milea-14934b299/> mentions Wolfram Institute affiliation; current status not independently verified.

### `SAHMED` — Sara Ahmed

- Not listed on Wolfram Institute /people page as of 2026-05-01.
- Personal site exists at <https://www.saranahmed.com/>; further verification not performed.

### `HKOLCZ` — Hubert Kolcz

- Not listed on Wolfram Institute /people page as of 2026-05-01.
- No further public record verified.

### `JPULLMAN` — Jan Pullman

- Not listed on Wolfram Institute /people page as of 2026-05-01.
- No further public record verified.

### `SRODKEY` — Sam Rodkey

- Not listed on Wolfram Institute /people page as of 2026-05-01.
- A GitHub user `SamRodkey` exists; whether this is the same person referenced in project docs is not independently verified.

---

## Repository / paclet ownership table

| Repository | Source of truth for "Creator" | git committers (per `git log` of clone) |
|---|---|---|
| `WolframInstitute/Infrageometry` | PacletInfo: NMURZIN | NMURZIN, PHAJEK, JWILES |
| `WolframInstitute/InfraAnalysis` | PacletInfo: PHAJEK | PHAJEK |
| `WolframInstitute/SyntheticInfrageometry` | PacletInfo: PHAJEK | PHAJEK |
| `WolframInstitute/InfraCausality` | PacletInfo: PHAJEK | PHAJEK |
| `WolframInstitute/InfraGaugeTheory` | PacletInfo: PPOKORNY | PHAJEK |
| `efficient_rewriting_final` (`HypergraphRewritingEngine`) | RASSAR (per project owner statement) | RASSAR |
| `infra_formalization` (this project) | RASSAR | RASSAR |

PacletInfo source files (clones in `resources/`): each `PacletInfo.wl` has a single `Creator` field; this is what the table records.

---

## How to use this file

- All project docs and Lean comments should refer to people by handle (`PHAJEK`, etc.).
- Bare first names in legacy docs (e.g. "Pavel said X") are being migrated to handles.
- Adding a new contributor: add a row to the handles table, then add a per-handle record below with verifiable evidence and citation.
- If you change a person's role at Wolfram Institute, re-fetch <https://wolframinstitute.org/people>, update the row, and bump the "Last verified" date at the top.
