#! /bin/bash
set -euo pipefail

nonest=$(tempfile --prefix="RT-nn")
proper=$(tempfile --prefix="RT-ps")
patience=$(tempfile --prefix="RT-pt")

cat hdiff/diff-{lua,java}.nonest.log   | grep "time(s)" | cut -d' ' -f6,7 | sed 's/\(time(s)\|n+m\)://g' > $nonest
cat hdiff/diff-{lua,java}.proper.log   | grep "time(s)" | cut -d' ' -f6,7 | sed 's/\(time(s)\|n+m\)://g' > $proper
cat hdiff/diff-{lua,java}.patience.log | grep "time(s)" | cut -d' ' -f6,7 | sed 's/\(time(s)\|n+m\)://g' > $patience

# Using 'ubuntu-mono' also looks pretty cool, gotta say
myfonts="../../tex/latex/fonts"

export GDFONTPATH=$myfonts
export GNUPLOT_FONTPATH=$myfonts

# http://triclinic.org/2015/04/publication-quality-plots-with-gnuplot/
gnuplot <<GNUPLOTSCRIPT
set terminal svg enhanced size 500,500 font 'STIX Two Math, 12'
set encoding iso_8859_1
set xlabel 'AST Size (n + m)'
set ylabel 'Time (s)'
# set logscale y 
# set logscale x

# set nokey
set key left top

set grid
# set yrange [0:1000]
set format x "%2.0t{/Symbol \327}10^{%L}"
# set format y "10^{%L}"


set xrange [100:70000]
set output '../img/runtimes-hdiff.svg'
plot '$nonest'   using 2:1 w dots lc 6 title 'nonest'\
   , '$proper'   using 2:1 w dots lc 2 title 'proper'\
   , '$patience' using 2:1 w dots lc 5 title 'patience'
GNUPLOTSCRIPT

# , 1.2e-7*x   title '  c{/Symbol \327}x'

