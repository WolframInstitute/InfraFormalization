/-
**F6: the initial data of arXiv:2102.09363 §6 is sampled from the
target geometry.**

**Paper text** (`papers/gorard_2102.09363.txt`).

  * Line 6080: the construction replaces "the assumption of weak
    ergodicity of the causal graph dynamics with the much stronger
    assumption of uniform Poisson distribution of the rewrite events".
  * Lines 6148-6152: the initial hypergraph `H` is constructed "by means
    of a Poisson point process" so that it is "guaranteed to be
    faithfully embeddable into a given Lorentzian manifold (M, g)".
  * Line 6179: this procedure sets up "the standard
    Brill-Lindquist binary black hole initial data".
  * Lines 6185-6192: the hypergraphs are coloured with the analytic
    Schwarzschild conformal factor `ψ` (eq. 391).

The paper gives no proof that the rule
`{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` produces
Poisson-distributed rewrite events, and its comparison starts from a
hypergraph sampled from the target initial-data geometry.

**This file.** `CircularReconstruction` is a pair of maps
`sample : Target → Sample` and `reconstruct : Sample → Target` together
with the hypothesis `reconstruct (sample t) = t`.
`CircularReconstruction.comp_eq_id` restates that hypothesis as an
equality of functions. The file does not model the procedure of
arXiv:2102.09363 and does not prove that the procedure satisfies the
hypothesis. The evolved hypergraphs at `t = 6M, 12M, 24M` are not the
sampled initial data, so the paper's comparison at those times is not
of the form `reconstruct ∘ sample`.
-/

namespace InfraFormalization
namespace Refutations

/-- A pair `(sample, reconstruct)` with `reconstruct ∘ sample = id`
assumed as the field `is_circular`. -/
structure CircularReconstruction (Target Sample : Type) where
  /-- Map from a target to a sample. -/
  sample : Target → Sample
  /-- Map from a sample to a target. -/
  reconstruct : Sample → Target
  /-- Hypothesis: reconstructing a sample of `t` returns `t`. -/
  is_circular : ∀ t : Target, reconstruct (sample t) = t

/-- The hypothesis `is_circular`, stated as an equality of functions. -/
theorem CircularReconstruction.comp_eq_id
    {Target Sample : Type} (cr : CircularReconstruction Target Sample) :
    (fun t => cr.reconstruct (cr.sample t)) = id := by
  funext t
  exact cr.is_circular t

end Refutations
end InfraFormalization
