#! /bin/bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  read -p "Should I gather the data myself? [Y/n] " ans
  case $ans in
    Y) aux=$(./prepare-runtimes.sh stdiff/diff-*) ;
       echo "Using data from: $aux";;
    *) echo "aborting"; exit 1;;
  esac
else
  aux=$1
fi


# Using 'ubuntu-mono' also looks pretty cool, gotta say
myfonts="../../tex/latex/fonts"

export GDFONTPATH=$myfonts
export GNUPLOT_FONTPATH=$myfonts

# http://triclinic.org/2015/04/publication-quality-plots-with-gnuplot/
gnuplot <<GNUPLOTSCRIPT
set terminal svg enhanced size 500,500 font 'STIX Two Math, 16'
set output '../img/runtimes-stdiff.svg'
set encoding iso_8859_1
# set xlabel 'AST Size (n + m)'
# set ylabel 'Time (s)'
set logscale y 
set logscale x

# set nokey
set key left top

set grid
set xrange [100:60000]
# set yrange [0:1000]
set format x "%2.0t{/Symbol \327}10^{%L}"
set format y "10^{%L}"
plot '$aux' using 2:1 w p pt 1 ps 0.3 lc 6 notitle\
   , 1.2e-7*x*x title '  c{/Symbol \327}x^2'\
   , 1.2e-7*x   title '  c{/Symbol \327}x'
GNUPLOTSCRIPT

