#! /bin/bash
set -euo pipefail

nonest=$(tempfile --prefix="RT-nn")
proper=$(tempfile --prefix="RT-ps")
patience=$(tempfile --prefix="RT-pt")

cat hdiff/diff-{lua,java}.nonest.log   | grep "time(s)" | cut -d' ' -f6,7 | sed 's/\(time(s)\|n+m\)://g' > $nonest
cat hdiff/diff-{lua,java}.proper.log   | grep "time(s)" | cut -d' ' -f6,7 | sed 's/\(time(s)\|n+m\)://g' > $proper
cat hdiff/diff-{lua,java}.patience.log | grep "time(s)" | cut -d' ' -f6,7 | sed 's/\(time(s)\|n+m\)://g' > $patience

# data for nonest and patience overlaps too much; I'll split
# the nonest file randomly into a bg and a fg part
nonestBG=$(tempfile --prefix="RT-nn")
nonestFG=$(tempfile --prefix="RT-nn")
./splitFile $nonest $nonestBG $nonestFG

# Using 'ubuntu-mono' also looks pretty cool, gotta say
myfonts="../../tex/latex/fonts"

export GDFONTPATH=$myfonts
export GNUPLOT_FONTPATH=$myfonts

# Awesome hack to increase pointsize in legend:
# https://stackoverflow.com/questions/12310236/gnuplot-increase-size-of-point-only-in-legend-key

# http://triclinic.org/2015/04/publication-quality-plots-with-gnuplot/
gnuplot <<GNUPLOTSCRIPT
set terminal svg enhanced size 500,500 font 'STIX Two Math, 16'
set encoding iso_8859_1
# set xlabel 'AST Size (n + m)'
# set ylabel 'Time (s)'
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
plot 1/0                   w p pt 2        lc 6 title 'nonest' \
   , '$nonestBG' using 2:1 w p pt 2 ps 0.2 lc 6 notitle \
   , 1/0                   w p pt 1        lc 2 title 'proper'\
   , '$proper'   using 2:1 w p pt 1 ps 0.2 lc 2 notitle \
   , 1/0                   w p pt 4        lc 5 title 'patience' \
   , '$patience' using 2:1 w p pt 4 ps 0.2 lc 5 notitle \
   , '$nonestFG' using 2:1 w p pt 2 ps 0.2 lc 6 notitle
GNUPLOTSCRIPT

# , 1.2e-7*x   title '  c{/Symbol \327}x'

