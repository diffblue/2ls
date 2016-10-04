git clone https://github.com/diffblue/cbmc
cd cbmc
CBMC=`pwd`
git checkout e4a5a611f569c72f97c0e099e56a827c9a55d2aa
cd src
make minisat2-download
make
cd ../../src
cp config.inc.template config.inc
sed -i.bak "s#CBMC = ~/my-cbmc#CBMC = $CBMC#g" config.inc
make
cd ..
echo "The executable is src/summarizer/2ls"
