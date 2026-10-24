(* Independent digitisation of the rPsi4 plots (G3 Figs 39, 49, 78, 84; Gravitas II Fig 54).
   Calibration from the image itself: the horizontal axis is the longest dark row (y = 0), the vertical
   axis the longest dark column; major ticks are the longest dark marks along each axis. The first
   major tick right of the vertical axis is t = 2 and major ticks are 2 apart in t; vertical major
   ticks are dy apart, dy read from the tick labels (0.002, or 0.001 for Fig 49). The curve is the
   mean row of the pixels within a colour distance of the series colour, per column.
   The calibration and the tracing share no code with scripts/python/digitise_rpsi4.py, which takes
   its tick pixels from scripts/python/axes_probe.py.
   Run: wolframscript -file scripts/digitise_rpsi4.wls
   Output: results/phase2_continuum/digitise_rpsi4_wl.out (printed) and
   results/phase2_continuum/digitise_rpsi4_wl.m (traces and curves on the common grid). *)
root = ParentDirectory[DirectoryName[$InputFileName]];
dir = FileNameJoin[{root, "papers"}];
outFile = FileNameJoin[{root, "results", "phase2_continuum", "digitise_rpsi4_wl.m"}];
figs = <|
  "G3 Fig 39 CCZ4 Schwarzschild" -> {FileNameJoin[{"tex_2102", "NumericalRelativity104.png"}], 0.002, {143, 176, 50}},
  "G3 Fig 78 rule Schwarzschild" -> {FileNameJoin[{"tex_2102", "NumericalRelativity177.png"}], 0.002, {143, 176, 50}},
  "G3 Fig 49 CCZ4 Kerr" -> {FileNameJoin[{"tex_2102", "NumericalRelativity132.png"}], 0.001, {143, 176, 50}},
  "G3 Fig 84 rule Kerr" -> {FileNameJoin[{"tex_2102", "NumericalRelativity178.png"}], 0.002, {143, 176, 50}},
  "GII Fig 54 Schwarzschild" -> {FileNameJoin[{"tex_2401", "GravitasFigure104.png"}], 0.002, {94, 129, 181}}|>;

dark[px_] := Max[px] < 0.62 && Max[px] - Min[px] < 0.08;
runLength[v_List] := Max[Append[Length /@ Select[Split[v], First[#] &], 0]];
calibrate[img_] := Module[{d = ImageData[ColorConvert[RemoveAlphaChannel[img], "RGB"]], h, w, dm, row, col, xt, yt, xmaj, ymaj, tick},
  {h, w} = Dimensions[d][[;; 2]];
  dm = Map[dark, d, {2}];
  row = First[Ordering[runLength /@ dm, -1]];
  col = First[Ordering[runLength /@ Transpose[dm], -1]];
  (* The extent of each axis line is its longest dark run. Ticks point up from the horizontal axis and
     right from the vertical axis; a tick's length is the dark run that starts next to the axis.
     Major ticks are the longest ticks within the extent of the axis. *)
  span[v_] := Module[{runs = Split[MapIndexed[{#1, First[#2]} &, v], #1[[1]] === #2[[1]] &]},
    MinMax[MaximalBy[Select[runs, #[[1, 1]] &], Length][[1]][[All, 2]]]];
  lead[v_] := LengthWhile[v, TrueQ];
  {x0, x1} = span[dm[[row]]]; {y0, y1} = span[dm[[All, col]]];
  xt = Table[If[x0 + 2 <= c <= x1 && Abs[c - col] > 3, lead[Reverse[dm[[Max[1, row - 10] ;; row - 1, c]]]], 0], {c, w}];
  yt = Table[If[y0 + 2 <= r <= y1 - 2 && r != row, lead[dm[[r, col + 1 ;; Min[w, col + 10]]]], 0], {r, h}];
  tick[v_] := With[{m = Max[v]}, Mean /@ Split[Flatten[Position[v, m]], #2 - #1 <= 2 &]];
  xmaj = Select[tick[xt], # > col + 3 &];
  ymaj = tick[yt];
  <|"Row" -> row, "Col" -> col, "XMajor" -> xmaj, "YMajor" -> ymaj|>];

trace[name_] := Module[{file, dy, colour, img, d, cal, x2, dx, ysp, pts},
  {file, dy, colour} = figs[name];
  img = Import[FileNameJoin[{dir, file}]];
  d = ImageData[ColorConvert[RemoveAlphaChannel[img], "RGB"]] 255.;
  cal = calibrate[img];
  x2 = cal["XMajor"][[1]]; dx = Mean[Differences[cal["XMajor"]]];
  ysp = Median[Differences[Sort[cal["YMajor"]]]];
  pts = DeleteCases[Table[With[{rows = Flatten[Position[Norm /@ (# - colour & /@ d[[All, c]]), x_ /; x < 45]]},
      If[rows === {} || c < cal["Col"] + 3, Nothing, {2 + 2 (c - x2)/dx, -(Mean[rows] - cal["Row"])/ysp dy}]], {c, Dimensions[d][[2]]}], Nothing];
  (* drop legend swatches: keep columns inside the plotted time range *)
  pts = Select[pts, 0.5 < #[[1]] < 12.5 &];
  <|"Name" -> name, "Calibration" -> cal, "TickSpacing" -> {dx, ysp}, "Points" -> pts|>];

traces = AssociationMap[trace, Keys[figs]];
Do[With[{t = traces[k]}, Print[k, ": axis row ", t["Calibration"]["Row"], ", axis column ", t["Calibration"]["Col"],
    ", major t ticks at ", Round[t["Calibration"]["XMajor"]], ", spacing ", Round[t["TickSpacing"], 0.1], ", points ", Length[t["Points"]],
    ", max ", MaximalBy[t["Points"], Last][[1]], ", min ", MinimalBy[t["Points"], Last][[1]]]], {k, Keys[traces]}];

grid = Range[1.4, 11.8, 0.02];
onGrid[k_] := Interpolation[DeleteDuplicatesBy[SortBy[traces[k]["Points"], First], First], InterpolationOrder -> 1] /@ grid;
curves = AssociationMap[onGrid, Keys[traces]];
corr[a_, b_] := Correlation[curves[a], curves[b]];
rms[a_, b_] := Sqrt[Mean[(curves[a] - curves[b])^2]];
pairs = {{"G3 Fig 39 CCZ4 Schwarzschild", "GII Fig 54 Schwarzschild"}, {"G3 Fig 39 CCZ4 Schwarzschild", "G3 Fig 78 rule Schwarzschild"},
  {"G3 Fig 49 CCZ4 Kerr", "G3 Fig 84 rule Kerr"}, {"G3 Fig 39 CCZ4 Schwarzschild", "G3 Fig 49 CCZ4 Kerr"},
  {"G3 Fig 78 rule Schwarzschild", "G3 Fig 84 rule Kerr"}};
Do[Print[p[[1]], " vs ", p[[2]], ": r = ", ToString[NumberForm[corr @@ p, {5, 4}]], ", RMS difference ", ToString[NumberForm[rms @@ p, 2, ExponentFunction -> (Null &)]]], {p, pairs}];
(* the Gravitas II system (M, M, 2M) is the G3 system scaled by 2: its curve against the G3 curve with time stretched by 2 *)
With[{f39 = Interpolation[DeleteDuplicatesBy[SortBy[traces["G3 Fig 39 CCZ4 Schwarzschild"]["Points"], First], First], InterpolationOrder -> 1],
    fG = Interpolation[DeleteDuplicatesBy[SortBy[traces["GII Fig 54 Schwarzschild"]["Points"], First], First], InterpolationOrder -> 1]},
  Do[With[{g = Select[grid, 1.4 <= #/s <= 11.8 &]}, Print["time stretch ", s, ": r = ", ToString[NumberForm[Correlation[fG /@ g, f39 /@ (g/s)], {5, 4}]], " over ", Length[g], " points"]], {s, {1, 2}}]];
Put[<|"Traces" -> traces, "Grid" -> grid, "Curves" -> curves|>, outFile];
