# Digitised rΨ4 curves of G3 and Gravitas II

## Plots compared

| Plot | Image file | Run | Source of the run parameters |
|---|---|---|---|
| G3 Figure 39 | `papers/tex_2102/NumericalRelativity104.png` (TeX line 2173) | CCZ4, Schwarzschild head-on collision, masses 0.5M, separation 1M, 200 to 800 vertices | `papers/gorard_2102.09363.txt` lines 4391-4440 |
| G3 Figure 49 | `papers/tex_2102/NumericalRelativity132.png` (TeX line 2315) | CCZ4, Kerr head-on collision | §5.5, from line 4556 |
| G3 Figure 78 | `papers/tex_2102/NumericalRelativity177.png` (TeX line 2992) | the rule of line 6202, Schwarzschild head-on collision | lines 6196-6246 |
| G3 Figure 84 | `papers/tex_2102/NumericalRelativity178.png` (TeX line 3084) | the rule, Kerr head-on collision | lines 6269-6463 |
| GII Figure 54 | `papers/tex_2401/GravitasFigure104.png` (`papers/tex_2401/GravitasPaper2.tex` lines 1326-1329) | ADM, 1 + log slicing, minimal distortion shift, masses M, separation 2M, 10,000 vertices, discretization scale 0.2M | `papers/tex_2401/GravitasPaper2.tex` lines 1226-1277, 1321, 1328 |

Each plot shows the real part of the ℓ = 2, m = 0 mode of rΨ4 against time in units of M. The G3 text states extraction on a sphere of radius 6M for all four G3 plots (TeX lines 2088, 2230, 2948 and 3040), and so do the captions of G3 Figures 39 and 78 (TeX lines 2174 and 2993) and GII line 1321. The captions of G3 Figures 49 and 84 state R = 60M (TeX lines 2316 and 3085). The G3 plots have three curves (200, 400 and 800 vertices). The comparison uses the 800-vertex curve (green, rendered pixels RGB 142, 176, 62). GII Figure 54 has one curve (blue, rendered pixels RGB 92, 129, 179). The scripts select pixels near the reference colours (143, 176, 50) and (94, 129, 181).

## Two digitisations

The two scripts share no code.

- `scripts/python/digitise_rpsi4.py` (Python, numpy and Pillow). The pixel positions of the labelled major ticks were read with `scripts/python/axes_probe.py` (output `results/phase2_continuum/axes_probe.out`) and are entered in the script. For each pixel column the curve value is the mean row of the pixels within colour distance 45 of the series colour. Comparisons are on t from 1.4 to 11.8 in steps of 0.02. Output: `results/phase2_continuum/digitise_rpsi4.out`.
- `scripts/digitise_rpsi4.wls` (Wolfram Language). The axes are the longest dark row and column of the image, and the major ticks are the longest dark marks along each axis. The time scale is taken from the tick spacing, and the vertical scale from the tick spacing and the tick labels (0.002, or 0.001 for G3 Figure 49). Output: `results/phase2_continuum/digitise_rpsi4_wl.out`, with the traces in `results/phase2_continuum/digitise_rpsi4_wl.m`.

Both scripts were run on 2026-10-24.

Calibration check: the Python digitisation reads the extrema of G3 Figure 39 as 0.00392 at t = 7.94 and −0.00381 at t = 6.76, and the Wolfram Language digitisation as 0.00388 at t = 7.93 and −0.00376 at t = 6.76. The plot shows a peak just below the 0.004 tick near t = 8 and a trough near t = 6.8.

## Results (MEASURED)

Pearson correlation r and RMS difference of the digitised curves on the common time grid:

| Pair | r (Python) | r (Wolfram Language) | RMS difference (Python) | RMS difference (Wolfram Language) |
|---|---:|---:|---:|---:|
| G3 Fig. 39 (CCZ4, Schwarzschild) against GII Fig. 54 | 1.000 | 0.9999 | 4.5 × 10⁻⁵ | 5.4 × 10⁻⁵ |
| G3 Fig. 39 (CCZ4, Schwarzschild) against G3 Fig. 78 (rule, Schwarzschild) | 0.998 | 0.9977 | 1.26 × 10⁻⁴ | 1.2 × 10⁻⁴ |
| G3 Fig. 49 (CCZ4, Kerr) against G3 Fig. 84 (rule, Kerr) | 0.995 | 0.9952 | 1.25 × 10⁻⁴ | 1.2 × 10⁻⁴ |
| Control: G3 Fig. 39 (CCZ4, Schwarzschild) against G3 Fig. 49 (CCZ4, Kerr) | 0.614 | 0.6120 | 1.54 × 10⁻³ | 1.5 × 10⁻³ |
| Control: G3 Fig. 78 (rule, Schwarzschild) against G3 Fig. 84 (rule, Kerr) | 0.621 | 0.6184 | 1.50 × 10⁻³ | 1.5 × 10⁻³ |

The RMS of the G3 Figure 39 curve is 1.83 × 10⁻³. One pixel is 2.5 × 10⁻⁵ in G3 Figure 39 and 2.1 × 10⁻⁵ in GII Figure 54, so the RMS difference between these two curves is about two pixels. A least-squares fit GII = a·G3(t − τ) + b gives a = 0.9996 and τ = −0.004 M, with a residual of 1.33 pixels. The 0.1-0.3 M wiggles of the 800-vertex G3 curve are present in the GII curve. After a moving average over 0.3M the Python correlations of the rule against CCZ4 are 0.999 (Schwarzschild) and 0.998 (Kerr).

Time rescaling. In vacuum, the GII system (masses M, separation 2M) is the G3 system (masses 0.5M, separation 1M) scaled by 2. In units of M its rΨ4 is the G3 curve stretched by 2 in time and halved in amplitude, and the extraction radius 6M is half the radius relative to the system size. Correlation of the GII Figure 54 curve with the G3 Figure 39 curve with the time axis stretched by a factor s:

| s | r (Python) | r (Wolfram Language) |
|---:|---:|---:|
| 1 | 1.000 | 0.9999 |
| 2 | 0.051 | 0.0837 |

The stretch test applies the time stretch but not the change of extraction radius. GII extracts at 6M, which corresponds to 3M in the G3 system, and G3 plots no curve at 3M. GII's window t = 1-12 maps to G3's t = 0.5-6, which ends before the merger peak of the G3 curve at t = 7.9, while the GII curve has that peak at t = 7.97.

## Findings

- The rΨ4 curves of the rule in G3 Figures 78 and 84 follow the CCZ4 curves of the same problem (r ≥ 0.995) and differ from the curves of the other problem as much as the two CCZ4 curves differ from each other (r ≈ 0.61-0.62). G3 gives no procedure that computes Ψ4 from a hypergraph (READ, lines 6210-6246).
- The rΨ4 curve of GII Figure 54 agrees with the 800-vertex CCZ4 curve of G3 Figure 39 to about two pixels, unstretched (amplitude ratio 0.9996, time offset 0.004 M), and carries the same 0.1-0.3 M wiggles. GII states a different formulation (ADM against CCZ4), resolution (10,000 vertices against 200-800) and system scale (masses M at separation 2M against 0.5M at 1M). With the time axis stretched by 2, the factor that relates the two systems, the correlation falls to 0.05-0.08. The stretch leaves the extraction radius unchanged (Time rescaling above).
