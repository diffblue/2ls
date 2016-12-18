git clone https://github.com/peterschrammel/cbmc
cd cbmc
CBMC=`pwd`
git checkout 1391879125f528ced5fe7e7ad1fd81afefb7bce2
cd src
make minisat2-download
make
cd ../../src
cp config.inc.template config.inc
sed -i.bak "s#CBMC = ~/my-cbmc#CBMC = $CBMC#g" config.inc
make
cd ..
echo "The executable is src/summarizer/2ls"
