#! /bin/bash

nocolor='s/\x1B\[([0-9]{1,3}(;[0-9]{1,2})?)?[mGK]//g'

for i in $(find -mindepth 1 -type d | grep suc-c); do
  pushd $i

  hdiff diff -d patience O.java A.java | sed -r $nocolor > OA.pt.patch
  hdiff diff -d patience O.java B.java | sed -r $nocolor > OB.pt.patch
  hdiff --debug merge -d patience A.java O.java B.java | sed -r $nocolor > R.pt.patch

  popd
done
