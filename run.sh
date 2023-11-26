#!/bin/sh
[ $# -lt 1 ] && exit 1
scriptpath=$(realpath $0)
scriptdir=$(dirname $scriptpath)
root=$(realpath $1)
cd $root
echo "1.64.0" > rust-toolchain
cargo rustc -- --emit=llvm-ir
[ $? -ne 0 ] && exit 1
irfile=$(realpath $(ls target/debug/deps/*.ll | head -n1))
code_root="."
if [ -d src ]; then
    code_root="src"
fi
python3 $scriptpath/tools/search.py $code_root > locations.txt
[ $? -ne 0 ] && exit 1
locationsfile=$(realpath locations.txt)
cd $scriptdir
make && \
    time bin/parser $irfile $locationsfile && \
    cp results.json $root/results.json
