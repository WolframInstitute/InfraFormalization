(* Run the Gorard "EFE" rule on a single seed specified by CLI arg.
   Usage: wolframscript -file run_seed.wl SEED_NAME MAX_EVENTS *)

Needs["SetReplace`"];

rule = {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
        Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}];

args = Rest[$ScriptCommandLine];
If[Length[args] < 2,
  Print["Usage: wolframscript -file run_seed.wl SEED_NAME MAX_EVENTS"];
  Exit[1]
];
seedName = args[[1]];
maxEvents = ToExpression[args[[2]]];

init = Switch[seedName,
  "4cycle", {{1, 2}, {2, 3}, {3, 4}, {4, 1}},
  "5path",  {{1, 2}, {2, 3}, {3, 4}, {4, 5}},
  "8cycle", Table[{i, Mod[i, 8] + 1}, {i, 8}],
  "6cycle", Table[{i, Mod[i, 6] + 1}, {i, 6}],
  "fig8",   Join[
              Table[{i, Mod[i, 6] + 1}, {i, 6}],
              Table[{i + 6, Mod[i, 6] + 7}, {i, 6}],
              {{1, 7}}],
  "twocy4", Join[
              Table[{i, Mod[i, 4] + 1}, {i, 4}],
              Table[{i + 4, Mod[i, 4] + 5}, {i, 4}]],
  "K4",     Flatten[Table[If[i == j, Nothing, {i, j}], {i, 4}, {j, 4}], 1],
  "10path", Table[{i, i+1}, {i, 10}],
  "20cycle", Table[{i, Mod[i, 20] + 1}, {i, 20}],
  _ , (Print["Unknown seed: ", seedName]; Exit[1])
];

Print["Seed ", seedName, " = ", init];
Print["MaxEvents = ", maxEvents];
mh = GenerateSingleHistory[
  MultisetSubstitutionSystem[rule], MaxEvents -> maxEvents
][init];

realEvents = Length[mh["EventInputs"]] - 1;
finalExprCount = Length[mh["Expressions"]];
termReason = mh["TerminationReason"];

Print["Real rule firings: ", realEvents];
Print["Final expression count: ", finalExprCount];
Print["Termination reason: ", termReason];
If[realEvents <= 4,
  Print["Final state: ", mh["Expressions"]]
];
