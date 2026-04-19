(* v3: use WolframModel (legacy interface, still supported) for clean
   property extraction. Run all seeds in ONE invocation to avoid
   paying the ~15 s startup cost multiple times. *)

Needs["SetReplace`"];

rule = {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
        Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}];

(* WolframModel[rule, init, {steps, ...}, property]; with maxEvents as
   the step spec via <|"MaxEvents" -> n|>. *)

(* Use PatternRules form to accept arbitrary delayed rules. *)
wrappedRule = <|"PatternRules" -> rule|>;

runSeed[label_String, init_List, maxEvents_Integer] := Module[
  {wm, finalState, cg},
  Print["\n=== ", label, " (|init|=", Length[init], ", MaxEvents=", maxEvents, ") ==="];
  wm = WolframModel[wrappedRule, init, <|"MaxEvents" -> maxEvents|>, "AllEventsCount"];
  Print["  Events fired: ", wm];
  If[NumericQ[wm],
    finalState = WolframModel[wrappedRule, init, <|"MaxEvents" -> maxEvents|>, "FinalState"];
    Print["  Final state size: ", Length[finalState]];
    If[wm <= 5, Print["  Final state: ", finalState]];
    If[wm >= 5,
      cg = WolframModel[wrappedRule, init, <|"MaxEvents" -> maxEvents|>, "CausalGraph"];
      Print["  Causal graph: vertices=", VertexCount[cg], ", edges=", EdgeCount[cg]];
    ];
  ];
];

runSeed["4-cycle seed",    {{1,2},{2,3},{3,4},{4,1}}, 200];
runSeed["5-path seed",     {{1,2},{2,3},{3,4},{4,5}}, 200];
runSeed["6-cycle seed",    Table[{i, Mod[i, 6] + 1}, {i, 6}], 500];
runSeed["8-cycle seed",    Table[{i, Mod[i, 8] + 1}, {i, 8}], 500];
runSeed["10-path seed",    Table[{i, i + 1}, {i, 10}], 500];
runSeed["20-cycle seed",   Table[{i, Mod[i, 20] + 1}, {i, 20}], 1000];
runSeed["figure-8",
  Join[Table[{i, Mod[i, 6] + 1}, {i, 6}],
       Table[{i + 6, Mod[i, 6] + 7}, {i, 6}],
       {{1, 7}, {7, 1}}],
  1000];
