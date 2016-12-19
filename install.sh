git clone https://github.com/peterschrammel/cbmc
cd cbmc
CBMC=`pwd`
git checkout d95e7da28018fd315b04a1201d5b7cfe8195cbc6
cd src
make minisat2-download
make
cd ../../src
cp config.inc.template config.inc
sed -i.bak "s#CBMC = ~/my-cbmc#CBMC = $CBMC#g" config.inc
make
cd ..
echo "The executable is src/summarizer/2ls"
