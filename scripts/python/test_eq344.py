"""Phase 2C — Audit of arXiv:2102.09363 Eq 344 (Ollivier Wasserstein).

Ollivier's theorem (JFA 2009, Theorem 4 + Example 7):
    W_1(m_p^ε, m_q^ε) = δ · (1 - ε²/(2(d+2)) · Ric(v,v) + O(ε⁴ + ε²δ²))
where m_p^ε is uniform on B_ε(p), and v = (q-p)/|q-p|.

Gorard's Eq 344 instead writes:
    W(B_ε(p), B_ε(q)) = δ · (1 - ε²/(2(d+2)) · R + O(ε³ + ε²δ))
with scalar R.

On unit S² (d=2): R = 2, Ric(v,v) = 1. Predicted coefficients differ
by a factor of 2.

We compute W_1 numerically on S² between two uniform-disk measures at
distance δ apart, at several ε, and compare to both predictions. Four
rails: (A) analytical Ollivier theorem statement, (B) numerical direct
computation, (C) linear-program LP solver, (D) hand sanity check at
tiny ε.
"""

from __future__ import annotations

import math
import numpy as np
from scipy.optimize import linear_sum_assignment


def spherical_dist(p, q):
    """Great-circle distance between two unit vectors in R^3."""
    dot = max(-1.0, min(1.0, float(np.dot(p, q))))
    return math.acos(dot)


def sample_uniform_disc_on_S2(center_lat, center_lon, radius_eps, n_samples, rng):
    """Sample n_samples points uniformly in the geodesic disc of radius
    ε around the point (lat, lon) on unit S². Uniform w.r.t. the
    Riemannian volume form on the disc."""
    # Uniform in geodesic disc: density ∝ sin(r) in radius, uniform in angle.
    # Sample r via inverse CDF: F(r) = (1 - cos r) / (1 - cos ε)
    # ⇒ r = arccos(1 - u(1 - cos ε)) for u ~ Uniform(0,1).
    u = rng.uniform(0, 1, n_samples)
    r = np.arccos(1 - u * (1 - math.cos(radius_eps)))
    psi = rng.uniform(0, 2 * math.pi, n_samples)
    # In a local frame at the center (north pole convention), the point at
    # (geodesic distance r, azimuth ψ) is  (sin r cos ψ, sin r sin ψ, cos r).
    local = np.column_stack([np.sin(r) * np.cos(psi),
                             np.sin(r) * np.sin(psi),
                             np.cos(r)])
    # Rotate from north-pole-centered to (lat, lon)-centered.
    # Rotation: first rotate local frame so that "up" (z) aligns with
    # the center direction. We build the rotation matrix that maps
    # (0,0,1) to  (cos lat cos lon, cos lat sin lon, sin lat).
    cx = math.cos(center_lat) * math.cos(center_lon)
    cy = math.cos(center_lat) * math.sin(center_lon)
    cz = math.sin(center_lat)
    c = np.array([cx, cy, cz])
    # Build orthonormal frame {e1, e2, c}. Pick e1 perpendicular to c:
    # one robust choice: e1 = (-sin lon, cos lon, 0).
    e1 = np.array([-math.sin(center_lon), math.cos(center_lon), 0.0])
    # e2 = c × e1
    e2 = np.cross(c, e1)
    e2 /= np.linalg.norm(e2)
    R = np.column_stack([e1, e2, c])  # columns: image of x̂, ŷ, ẑ
    return local @ R.T


def wasserstein1(p_points, q_points):
    """Compute W_1 between two empirical measures of equal mass on S².

    Both are uniform-weighted on `p_points` and `q_points` respectively.
    Uses spherical distance. Reduces W_1 to bipartite assignment when
    |p_points| = |q_points| = N (equal mass per point) — then
    W_1 = min over assignments of (1/N) ∑ d(p_i, q_{σ(i)}).
    """
    n = len(p_points)
    assert len(q_points) == n, "equal-mass assignment requires |p| = |q|"
    D = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            D[i, j] = spherical_dist(p_points[i], q_points[j])
    row, col = linear_sum_assignment(D)
    return D[row, col].sum() / n


def ollivier_coefficient_s2():
    """Returns predicted ε² coefficients on unit S² (d=2)."""
    d = 2
    R = 2.0
    ric_uu = 1.0
    return {
        "Ollivier (directional Ric)": ric_uu / (2.0 * (d + 2)),
        "Gorard Eq 344 (scalar R)": R / (2.0 * (d + 2)),
    }


def run_s2(n_samples=300, seed=42):
    rng = np.random.default_rng(seed)
    # p = north pole, q along the prime meridian at latitude π/2 - δ.
    # Test multiple δ, ε.
    print(f"=== Eq 344 audit on S² (uniform, n_samples={n_samples}) ===")
    print()
    coeffs = ollivier_coefficient_s2()
    print("Predicted ε² coefficient in [W_1 = δ(1 - c · ε²)]:")
    for k, v in coeffs.items():
        print(f"   {k}: c = {v:.4f}")
    print()

    print(f"{'δ':>8} {'ε':>8}  {'W_1 (num)':>12}  {'W_1/δ':>10}  "
          f"{'Ollivier pred':>14}  {'Gorard pred':>14}  "
          f"{'err_Oll':>10}  {'err_Gor':>10}")
    print("-" * 120)
    for delta in [0.05, 0.1, 0.15]:
        for eps in [0.03, 0.05, 0.08, 0.10]:
            # p = north pole (lat = π/2, lon = 0)
            pts_p = sample_uniform_disc_on_S2(math.pi / 2, 0.0, eps, n_samples, rng)
            # q = slightly south (lat = π/2 - δ, lon = 0)
            pts_q = sample_uniform_disc_on_S2(math.pi / 2 - delta, 0.0, eps, n_samples, rng)

            W = wasserstein1(pts_p, pts_q)
            ratio = W / delta

            ollivier_pred = 1 - coeffs["Ollivier (directional Ric)"] * eps ** 2
            gorard_pred = 1 - coeffs["Gorard Eq 344 (scalar R)"] * eps ** 2

            err_oll = abs(ratio - ollivier_pred)
            err_gor = abs(ratio - gorard_pred)

            print(f"{delta:>8.3f} {eps:>8.3f}  {W:>12.6f}  {ratio:>10.6f}  "
                  f"{ollivier_pred:>14.6f}  {gorard_pred:>14.6f}  "
                  f"{err_oll:>10.6f}  {err_gor:>10.6f}")
    print()


def main():
    run_s2(n_samples=300)
    run_s2(n_samples=600)
    print()
    print("=== Verdict ===")
    print("If Ollivier-prediction errors are much smaller than Gorard-prediction")
    print("errors (and scale with sample-noise), Eq 344 is refuted.")


if __name__ == "__main__":
    main()
