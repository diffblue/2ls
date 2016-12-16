git clone https://github.com/peterschrammel/cbmc
cd cbmc
CBMC=`pwd`
git checkout f8c51ebc26be795046f9311217ef1a2809306330
cd src
make minisat2-download
make
cd ../../src
cp config.inc.template config.inc
sed -i.bak "s#CBMC = ~/my-cbmc#CBMC = $CBMC#g" config.inc
make
cd ..
echo "The executable is src/summarizer/2ls"
