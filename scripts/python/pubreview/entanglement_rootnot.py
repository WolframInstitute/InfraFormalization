"""Path counts against amplitudes for the root-NOT example of arXiv:2301.12455
(papers/tex_2301_12455/EntanglementEntropy.tex lines 1788-1824, Figures 26-27).

G9 builds a multiway graph by applying sqrt(NOT) = (1/2)[[1+i, 1-i], [1-i, 1+i]] to
(|0> + |1>)/sqrt(2), and assigns each state "a numerical weight based on the number of distinct
evolution paths ... leading to that state, interpreted as a (magnitude of a) quantum amplitude".
Every entry of sqrt(NOT) is non-zero, so each basis state has both basis states as successors.
The script compares, for t = 0..6, the normalised path counts with the moduli of the amplitudes
of sqrt(NOT)^t |psi0>, for |psi0> = (|0> + |1>)/sqrt(2) (G9's initial state) and |psi0> = |0>."""
import json

import numpy as np

ROOT_NOT = 0.5 * np.array([[1 + 1j, 1 - 1j], [1 - 1j, 1 + 1j]])


def run(psi0, counts0):
    rows = []
    psi = np.array(psi0, dtype=complex)
    counts = np.array(counts0, dtype=float)
    for t in range(7):
        amp = np.abs(psi)
        w = counts / np.linalg.norm(counts)
        rows.append({"t": t, "path_counts": counts.tolist(),
                     "normalised_counts": np.round(w, 4).tolist(),
                     "amplitude_moduli": np.round(amp, 4).tolist(),
                     "max_difference": round(float(np.max(np.abs(w - amp))), 4)})
        psi = ROOT_NOT @ psi
        counts = np.array([counts.sum(), counts.sum()])
    return rows


def main():
    s = 1 / np.sqrt(2)
    out = {"plus_state": run([s, s], [1, 1]), "zero_state": run([1, 0], [1, 0]),
           "sqrtnot_squared_equals_not": bool(np.allclose(ROOT_NOT @ ROOT_NOT,
                                                          [[0, 1], [1, 0]]))}
    print(json.dumps(out, indent=1))
    with open("../../../results/publication_review/entanglement_rootnot.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
