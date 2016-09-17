git clone https://github.com/peterschrammel/cbmc
cd cbmc
CBMC=`pwd`
git checkout e347c69bb1071f174f611278f5e001fd6070884a
cd src
make minisat2-download
make
cd ../../src
cp config.inc.template config.inc
sed -i.bak "s#CBMC = ~/my-cbmc#CBMC = $CBMC#g" config.inc
make
cd ..
echo "The executable is src/summarizer/2ls"
