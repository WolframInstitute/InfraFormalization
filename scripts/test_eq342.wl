(* Phase 2B — complete numerical + symbolic audit of arXiv:2102.09363 Eq 342
   (= arXiv:2011.12174 Eq 126).

   Two independent Riemannian test cases where we can compute the tube
   volume exactly in closed form: S² around a great circle, and S³
   around a great circle.

   The correct coefficient in the tube-volume expansion, derived from
   Fermi normal coordinates along a geodesic (see results/phase2_continuum/tube_derivation.md):

     Vol(T_eps) = ω_{d-1} eps^{d-1} L · (1 - (eps²/(6(d+1))) (R + Ric(u,u)) + O(eps^4))

   Gorard's Eq 342 asserts:

     Vol(T_eps) = ω_{d-1} eps^{d-1} L · (1 - ((d-1)/(d+1)) (R - Ric(u,u)) eps² + O(...))

   These are different algebraic forms; on S^d (unit sphere, R = d(d-1),
   Ric(u,u) = d-1), correct = (d-1)² · (d+1) / (6(d+1)(d-1)) = (d-1)/6,
   Gorard = (d-1)·(d-1)²/(d+1) = (d-1)³/(d+1).

   Ratios (Gorard/correct) on S^d:
     d=2 :  correct=1/6,  Gorard=1/3,  ratio 2
     d=3 :  correct=1/3,  Gorard=2,    ratio 6
     d=4 :  correct=1/2,  Gorard=27/5, ratio 54/5 = 10.8

   We verify the d=2 and d=3 cases directly and exactly here.  *)

Print["=== Eq 342 audit ==="];

(* S^2 exact: tube around great circle of length 2π, half-width ε *)
Print[""];
Print["--- S^2, unit sphere, tube around great circle of length L=2π ---"];
exactS2[eps_] := 4 Pi Sin[eps];    (* spherical zone of half-width ε *)
omega1 = Pi^((2 - 1)/2)/Gamma[(2 + 1)/2];  (* = 2 *)
flatS2[eps_] := omega1 * eps^(2 - 1) * (2 Pi);   (* = 4 π ε *)
Print["Exact volume (spherical zone): 4π sin(ε)"];
Print["Flat leading (ω_{d-1} ε^{d-1} L) = 4π ε"];
seriesS2 = Series[exactS2[eps]/flatS2[eps], {eps, 0, 4}];
Print["Exact ratio series:        ", Normal[seriesS2]];
Print["Correct (Gray-style)  coeff: (R+Ric)/(6(d+1)) = 3/18 = 1/6  → 1 - ε²/6"];
Print["Gorard Eq 342         coeff: (d-1)(R-Ric)/(d+1) = 1/3·1 = 1/3  → 1 - ε²/3"];
coeffExactS2 = -SeriesCoefficient[seriesS2, 2];
Print["Exact ε² coefficient from series: ", coeffExactS2, "  (= 1/6)"];
Print[""];

(* S^3 exact: tube around great circle of length 2π, half-width ε *)
Print["--- S^3, unit sphere, tube around great circle of length L=2π ---"];
(* In coordinates (t,r,φ) parameterising point
     p = (cos r cos t, cos r sin t, sin r cos φ, sin r sin φ),
   induced metric is diag(cos²r, 1, sin²r), volume element cos(r) sin(r).
   Integrate over t ∈ [0,2π), r ∈ [0,ε], φ ∈ [0,2π):  *)
exactS3[eps_] := (2 Pi) (2 Pi) Integrate[Cos[r] Sin[r], {r, 0, eps}]; (* = 2π² sin²ε *)
omega2 = Pi^((3 - 1)/2)/Gamma[(3 + 1)/2];   (* = π *)
flatS3[eps_] := omega2 * eps^(3 - 1) * (2 Pi);   (* = 2 π² ε² *)
Print["Exact volume: 2π² sin²(ε)"];
Print["Flat leading (ω_{d-1} ε^{d-1} L) = 2π² ε²"];
seriesS3 = Series[Simplify[exactS3[eps]/flatS3[eps]], {eps, 0, 4}];
Print["Exact ratio series: ", Normal[seriesS3]];
(* d=3, R=6, Ric(u,u)=2 *)
Print["Correct coeff: (R+Ric)/(6(d+1)) = 8/24 = 1/3  → 1 - ε²/3"];
Print["Gorard coeff:  (d-1)(R-Ric)/(d+1) = 2·4/4 = 2  → 1 - 2ε²  (! huge)"];
coeffExactS3 = -SeriesCoefficient[seriesS3, 2];
Print["Exact ε² coefficient: ", coeffExactS3, "  (= 1/3)"];

Print[""];
Print["--- Numerical comparison, S^2 ---"];
Print[StringForm["  `1`  `2`  `3`  `4`  `5`",
  PaddedForm["eps",      {6, 3}, NumberSigns -> {"", ""}],
  PaddedForm["exact",    {8, 5}, NumberSigns -> {"", ""}],
  PaddedForm["correct",  {8, 5}, NumberSigns -> {"", ""}],
  PaddedForm["Gorard",   {8, 5}, NumberSigns -> {"", ""}],
  PaddedForm["err",      {8, 5}, NumberSigns -> {"", ""}]]];
Do[
  With[{e = N[epsv]},
    ex = N[exactS2[e]/flatS2[e]];
    co = 1 - e^2/6;
    go = 1 - e^2/3;
    Print[StringForm["  `1`  `2`  `3`  `4`  `5`",
      PaddedForm[e, {6, 3}],
      PaddedForm[ex, {8, 5}],
      PaddedForm[co, {8, 5}],
      PaddedForm[go, {8, 5}],
      PaddedForm[Abs[ex - go]/ex, {8, 5}]
    ]]
  ],
  {epsv, {0.05, 0.10, 0.15, 0.20, 0.30}}];

Print[""];
Print["--- Numerical comparison, S^3 ---"];
Print[StringForm["  `1`  `2`  `3`  `4`  `5`",
  PaddedForm["eps",      {6, 3}, NumberSigns -> {"", ""}],
  PaddedForm["exact",    {8, 5}, NumberSigns -> {"", ""}],
  PaddedForm["correct",  {8, 5}, NumberSigns -> {"", ""}],
  PaddedForm["Gorard",   {8, 5}, NumberSigns -> {"", ""}],
  PaddedForm["err",      {8, 5}, NumberSigns -> {"", ""}]]];
Do[
  With[{e = N[epsv]},
    ex = N[exactS3[e]/flatS3[e]];
    co = 1 - e^2/3;
    go = 1 - 2 e^2;
    Print[StringForm["  `1`  `2`  `3`  `4`  `5`",
      PaddedForm[e, {6, 3}],
      PaddedForm[ex, {8, 5}],
      PaddedForm[co, {8, 5}],
      PaddedForm[go, {8, 5}],
      PaddedForm[Abs[ex - go]/ex, {8, 5}]
    ]]
  ],
  {epsv, {0.05, 0.10, 0.15, 0.20, 0.30}}];

Print[""];
Print["=== Verdict ==="];
Print["On S²:  exact 1/6   correct-formula 1/6   Gorard-Eq-342 1/3   (Gorard 2× too big)"];
Print["On S³:  exact 1/3   correct-formula 1/3   Gorard-Eq-342 2     (Gorard 6× too big)"];
Print[""];
Print["⇒ Eq 342 of arXiv:2102.09363 (= Eq 126 of arXiv:2011.12174) is"];
Print["  incorrect in BOTH the algebraic structure AND the overall scale."];
