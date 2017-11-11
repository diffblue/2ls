#!/bin/bash

CBMC_REPO=https://github.com/peterschrammel/cbmc
CBMC_VERSION=2ls-prerequisites-0.6

if [ "$1" != "" ]
then
  COMPILER="$1"
fi

git clone $CBMC_REPO
cd cbmc
CBMC=`pwd`
git checkout $CBMC_VERSION
if grep '^MINISAT2' src/config.inc > /dev/null
then
  make -C src minisat2-download > /dev/null
elif grep '^GLUCOSE' src/config.inc
then
  make -C src glucose-download
else
  echo "SAT solver not supported"
  exit 1
fi
if [ "$COMPILER" != "" ]
then
  make -C src CXX=$COMPILER
else
  make -C src
fi

cd ../src
cp config.inc.template config.inc
sed -i.bak "s#CBMC = ~/my-cbmc#CBMC = $CBMC#g" config.inc
if [ "$COMPILER" != "" ]
then
  make CXX=$COMPILER
else
  make
fi
cd ..
echo "The executable is src/2ls/2ls"
