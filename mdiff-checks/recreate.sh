#! /bin/bash

function doOne() {
  pushd $1
  read -r lang height mode scope rest < origin

  ## little processing
  lang=${lang#*-}; lang=${lang%%\.1*}

  scopeopt=""
  if [[ "$scope" == "global" ]]; then
    scopeopt="--global-scope"
  fi

  hdiff -v merge -d $mode -m $height $scopeopt A.$lang O.$lang B.$lang > R.ast

  hdiff ast M.$lang > M.ast

  popd
}

for i in $(find -mindepth 1 -type d); do
  doOne $i
done
