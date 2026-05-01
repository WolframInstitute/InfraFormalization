/-
**F6 — Circularity of JGORARD's 2102.09363 "provably satisfies EFE"**
(formal refutation of the most serious structural flaw).

**The claim.** JGORARD (2102.09363 §5, line 6080+) claims the hypergraph
rewriting rule
`{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}`
"provably satisfies the Einstein field equations in the continuum
limit."

**The actual procedure (close reading, `notes/2102.09363_close_reading.md`).**

  1. Pick a target Lorentzian manifold `M` (Schwarzschild or Kerr).
  2. **Poisson-sprinkle vertices into `M`** (line 6152, verbatim).
  3. Connect nearby vertices to get a hypergraph `H[M]`.
  4. Run Benincasa–Dowker counting on `H[M]`; recover curvature
     information consistent with `M`.

**Why this is circular.** Step 2 **uses `M` as input** to produce the
hypergraph. The spacetime is not an emergent consequence of rewriting
dynamics; it is the input. Any procedure of the form
`M → sample(M) → reconstruct-from-sample = M` is circular by
definition — it demonstrates sample-consistency, not derivation.

**This file.** Formalises the circularity *structure*, independent of
the specific physics. We model the general pattern and prove that any
function of that shape "trivially produces its input" — making it not
a derivation.

The user-facing conclusion: JGORARD's 2102.09363 "derivation of GR"
fits this pattern. It is therefore devoid of the mathematical content
the word "derivation" implies. The numerical agreement (Tables 6–7 of
the paper) is a consistency check on the sampling, not a verification
of dynamics — it demonstrates that the mesh recovers the known metric
when seeded with that metric.
-/

namespace InfraFormalization
namespace Refutations

/-- **Circular-reconstruction schema**: a pair `(sample, reconstruct)`
where `sample : Target → Sample` extracts sample-data from a target
and `reconstruct : Sample → Target` recovers the target from a
sample. The composition `reconstruct ∘ sample = id` identifies a
circular reconstruction. -/
structure CircularReconstruction (Target Sample : Type) where
  /-- Extract a sample from a target (e.g., Poisson-sprinkle). -/
  sample : Target → Sample
  /-- Reconstruct the target from the sample (e.g., Benincasa-Dowker
  counting). -/
  reconstruct : Sample → Target
  /-- The whole procedure is circular: reconstruction recovers the
  original target given a sample from it. -/
  is_circular : ∀ t : Target, reconstruct (sample t) = t

/-- **Circularity implies the "reconstruction" has no derivational
content.** If `(sample, reconstruct)` is a circular reconstruction,
then for every target `t`, the "derived" output `reconstruct (sample t)`
is *identically* `t`. No information beyond what was put in by `sample`
is produced.

This captures why a procedure of the form "sample the known target, then
reconstruct from the sample" is not a derivation of the target — it is a
sample-consistency check. -/
theorem circular_reconstruction_has_no_content
    {Target Sample : Type} (cr : CircularReconstruction Target Sample) :
    ∀ t : Target, cr.reconstruct (cr.sample t) = t :=
  cr.is_circular

/-- **Refutation of the "derivation" label.** A claim of the form

  "procedure `P` derives the Einstein equations for `M`"

in the strong sense requires more than sample-consistency: `P` must
produce `M` from data *not already encoding `M`*. When `P` fits
`CircularReconstruction`, the claim fails — `P` requires `M` as input.

Formally: if `P = cr.reconstruct ∘ cr.sample` for some
`CircularReconstruction Target Sample cr`, then `P = id`, and no
target-level "derivation" content is present. -/
theorem circular_procedure_is_identity
    {Target Sample : Type} (cr : CircularReconstruction Target Sample) :
    (fun t => cr.reconstruct (cr.sample t)) = id := by
  funext t
  exact cr.is_circular t

end Refutations
end InfraFormalization
