#!/usr/bin/env gnuplot
# bench/plot.gp — Generate bench_results.png from bench_results.tsv
#
# Usage: gnuplot plot.gp
#   or:  gnuplot -e "tsv='other.tsv'" plot.gp

if (!exists("tsv")) tsv = "bench_results.tsv"

set terminal pngcairo size 1400,900 enhanced font "sans,11"
set output "bench_results.png"

set multiplot layout 2,2 title "Elias-Fano Benchmark — 4 implementations, 1K–100M elements" font ",13"

# --- Shared settings ---
set logscale xy
set grid
set key top left font ",9"
set format x "%.0s%c"

# --- Styles ---
set style line 1 lc rgb "#e41a1c" lw 2 pt 7 ps 0.8   # sux - red
set style line 2 lc rgb "#377eb8" lw 2 pt 9 ps 0.8   # sdsl - blue
set style line 3 lc rgb "#4daf4a" lw 2 pt 5 ps 0.8   # ocaml - green
set style line 4 lc rgb "#984ea3" lw 2 pt 13 ps 0.8  # extracted - purple

# --- access ---
set title "access (ns/query)"
set xlabel "n"
set ylabel "ns/query"
plot \
  "< awk -F'\\t' '$1==\"sux\" && $3==\"access\"' ".tsv       using 2:4 with linespoints ls 1 title "sux", \
  "< awk -F'\\t' '$1==\"sdsl\" && $3==\"access\"' ".tsv      using 2:4 with linespoints ls 2 title "sdsl", \
  "< awk -F'\\t' '$1==\"ocaml\" && $3==\"access\"' ".tsv     using 2:4 with linespoints ls 3 title "ocaml", \
  "< awk -F'\\t' '$1==\"extracted\" && $3==\"access\"' ".tsv  using 2:4 with linespoints ls 4 title "extracted"

# --- nextGEQ ---
set title "nextGEQ (ns/query)"
set ylabel "ns/query"
plot \
  "< awk -F'\\t' '$1==\"sux\" && $3==\"nextGEQ\"' ".tsv       using 2:4 with linespoints ls 1 title "sux", \
  "< awk -F'\\t' '$1==\"sdsl\" && $3==\"nextGEQ\"' ".tsv      using 2:4 with linespoints ls 2 title "sdsl", \
  "< awk -F'\\t' '$1==\"ocaml\" && $3==\"nextGEQ\"' ".tsv     using 2:4 with linespoints ls 3 title "ocaml", \
  "< awk -F'\\t' '$1==\"extracted\" && $3==\"nextGEQ\"' ".tsv  using 2:4 with linespoints ls 4 title "extracted"

# --- decode ---
set title "decode (total ms)"
set ylabel "ms"
plot \
  "< awk -F'\\t' '$1==\"sux\" && $3==\"decode\"' ".tsv       using 2:($4/1e6) with linespoints ls 1 title "sux", \
  "< awk -F'\\t' '$1==\"sdsl\" && $3==\"decode\"' ".tsv      using 2:($4/1e6) with linespoints ls 2 title "sdsl", \
  "< awk -F'\\t' '$1==\"ocaml\" && $3==\"decode\"' ".tsv     using 2:($4/1e6) with linespoints ls 3 title "ocaml", \
  "< awk -F'\\t' '$1==\"extracted\" && $3==\"decode\"' ".tsv  using 2:($4/1e6) with linespoints ls 4 title "extracted"

# --- encode ---
set title "encode (total ms)"
set ylabel "ms"
plot \
  "< awk -F'\\t' '$1==\"sux\" && $3==\"encode\"' ".tsv       using 2:($4/1e6) with linespoints ls 1 title "sux", \
  "< awk -F'\\t' '$1==\"sdsl\" && $3==\"encode\"' ".tsv      using 2:($4/1e6) with linespoints ls 2 title "sdsl", \
  "< awk -F'\\t' '$1==\"ocaml\" && $3==\"encode\"' ".tsv     using 2:($4/1e6) with linespoints ls 3 title "ocaml", \
  "< awk -F'\\t' '$1==\"extracted\" && $3==\"encode\"' ".tsv  using 2:($4/1e6) with linespoints ls 4 title "extracted"

unset multiplot
