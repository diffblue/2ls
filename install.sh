git clone https://github.com/peterschrammel/cbmc
cd cbmc
CBMC=`pwd`
git checkout f24b105d00acb63f3cbe6a13623307258b08a812
cd src
make minisat2-download
make
cd ../../src
cp config.inc.template config.inc
sed -i.bak "s#CBMC = ~/my-cbmc#CBMC = $CBMC#g" config.inc
make
cd ..
echo "The executable is src/summarizer/2ls"
