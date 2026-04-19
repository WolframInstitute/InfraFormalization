(* Phase 2B — triple-redundant numerical test of arXiv:2102.09363 Eq 342.

   Eq 342 (from the paper's TeX source, line 2607 of NumericalRelativity.tex):

     Vol(T_{ε, δx}(p)) = (π^{(d-1)/2} / Γ((d+1)/2)) · ε^{d-1} · |δx|
       · (1 - ((d-1)/(d+1)) · (R - Ric_{ij} δxhat^i δxhat^j) · ε²
         + O(ε³ + ε²|δx|) + ...)

   Correct Gray tube formula (Gray, "Tubes" 2nd ed. §2.5; Gray-Vanhecke
   Acta Math 1979 §4):

     Vol(T_ε(γ)) = ω_{d-1} · ε^{d-1} · L
       · (1 - (ε² / (2(d+1))) · (R - Ric(u,u)) + O(ε⁴))

   where γ is a geodesic of length L with unit tangent u, and ω_{d-1}
   = π^{(d-1)/2}/Γ((d+1)/2).

   Gorard coefficient: (d-1)/(d+1)   (in front of (R - Ric(u,u)) ε²)
   Gray coefficient:   1/(2(d+1))

   Predicted discrepancy ratio: Gorard / Gray = 2(d-1).
     d=2 → factor 2;  d=3 → factor 4;  d=4 → factor 6.

   ------------------------------------------------------------------
   Test on S² (unit round sphere, d=2).

   Exact tube around a great circle of length L = 2π at half-width ε:
   spherical zone area A(ε) = 4π sin(ε).
   Expand: A(ε) = 4πε (1 - ε²/6 + ε⁴/120 - ...).
   So the tube-correction coefficient at O(ε²) is **1/6**.

   At d=2:
     R = 2 (unit sphere scalar curvature)
     Ric(u, u) = 1   (any unit direction on unit sphere)
     R - Ric(u, u) = 1.
   Predictions:
     Gray:   1/(2(d+1)) · 1 = 1/6     ← matches exact
     Gorard: (d-1)/(d+1)  · 1 = 1/3   ← double the exact value

   We verify this symbolically + numerically here.  *)

Print["=== Phase 2B — Eq 342 verification on S^2 ==="];
Print[""];

(* (A) Exact tube area on S^2 around a great circle as a function of ε. *)
Print["(A) Exact S^2 tube area around great circle, length L = 2π:"];
ExactArea[eps_, L_] := 2 L Sin[eps];  (* = L * 2 sin ε, for any tube length L on S² *)
Print["     A(ε, L) = 2 L sin(ε)"];
Print["     A(ε, 2π) = 4π sin(ε)"];
Print["     Series expansion: ",
  Normal[Series[ExactArea[eps, 2 Pi] / (4 Pi eps), {eps, 0, 4}]]];
Print[""];

(* (B) Gorard's Eq 342 prediction for S² (d=2, R=2, Ric(u,u)=1). *)
d = 2;
R = 2;
RicUU = 1;
Print["(B) Gorard Eq 342 prediction:"];
omegaDM1 = Pi^((d - 1)/2) / Gamma[(d + 1)/2];   (* = 2 for d=2 *)
Print["     ω_{d-1} = π^{(d-1)/2}/Γ((d+1)/2) = ", omegaDM1,
  "  (= 2 for d=2, giving prefactor 2 ε L)"];
gorardCoeff = ((d - 1)/(d + 1)) * (R - RicUU);
Print["     correction coeff at ε²: (d-1)/(d+1) · (R - Ric(u,u)) = ",
  gorardCoeff, "  (= 1/3)"];
Print["     prediction: V_tube / (ω_{d-1} ε^{d-1} L) = 1 - (1/3) ε² + O(ε^4)"];
Print[""];

(* (C) Gray's (correct) prediction. *)
Print["(C) Gray's (correct) prediction:"];
grayCoeff = (1/(2 (d + 1))) * (R - RicUU);
Print["     correction coeff at ε²: 1/(2(d+1)) · (R - Ric(u,u)) = ",
  grayCoeff, "  (= 1/6)"];
Print["     prediction: V_tube / (ω_{d-1} ε^{d-1} L) = 1 - (1/6) ε² + O(ε^4)"];
Print[""];

(* (D) Exact value of the correction coefficient from (A). *)
Print["(D) Exact value of the O(ε²) correction coefficient from (A):"];
exactSeries = Series[ExactArea[eps, 2 Pi] / (omegaDM1 * eps^(d - 1) * 2 Pi), {eps, 0, 4}];
Print["     ", Normal[exactSeries]];
Print["     ⇒ O(ε²) coefficient = ", SeriesCoefficient[exactSeries, 2]];
Print[""];

(* (E) Numerical test at several ε. *)
Print["(E) Numerical comparison at several ε:"];
testEps = {0.05, 0.1, 0.15, 0.2, 0.3};
Print[StringForm["     ``10s `` `10s` `10s` `10s` `10s`",
  "ε", "exact ratio", "(1-ε²/6)", "(1-ε²/3)", "|diff/exact|"]];
Do[
  With[{e = N[epsv]},
    exact = ExactArea[e, 2 Pi] / (omegaDM1 * e * 2 Pi);
    grayPred = 1 - e^2/6;
    gorardPred = 1 - e^2/3;
    Print[StringForm["   `` `` `` `` `` ``",
      PaddedForm[e, {5, 3}],
      PaddedForm[exact, {9, 6}],
      PaddedForm[grayPred, {9, 6}],
      PaddedForm[gorardPred, {9, 6}],
      PaddedForm[Abs[exact - gorardPred]/exact, {8, 5}]
    ]];
  ],
  {epsv, testEps}
];
Print[""];

(* (F) Verdict. *)
Print["(F) Verdict:"];
Print["     Exact coefficient = 1/6."];
Print["     Gray's formula (correct)   = 1/6.          ✓"];
Print["     Gorard's Eq 342 prediction = 1/3.          ✗ off by factor 2"];
Print[""];
Print["     The predicted Gorard/Gray ratio 2(d-1) evaluates to 2 at d=2,"];
Print["     consistent with the observed factor 2 discrepancy above."];
Print[""];
Print["=== Phase 2B — DONE ==="];
